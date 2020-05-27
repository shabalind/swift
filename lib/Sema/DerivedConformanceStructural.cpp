//
// This source file is part of the Swift.org open source project
//
// Copyright (c) 2016 Apple Inc. and the Swift project authors
// Licensed under Apache License v2.0 with Runtime Library Exception
//
// See http://swift.org/LICENSE.txt for license information
// See http://swift.org/CONTRIBUTORS.txt for the list of Swift project authors
//
//===----------------------------------------------------------------------===//
//
//  This file implements implicit derivation of the CaseIterable protocol.
//
//===----------------------------------------------------------------------===//

// clang-format off
#include "TypeChecker.h"
#include "swift/AST/Decl.h"
#include "swift/AST/Stmt.h"
#include "swift/AST/Expr.h"
#include "swift/AST/Types.h"
#include "swift/AST/ParameterList.h"
#include "llvm/Support/raw_ostream.h"
#include "DerivedConformances.h"
// clang-format on

using namespace swift;

namespace {

StructDecl *deriveStructural_lookupStructDecl(swift::ASTContext &C, 
                                           ModuleDecl *structuralCoreDecl,
                                           swift::Identifier id) {
  SmallVector<ValueDecl *, 1> results;
  structuralCoreDecl->lookupValue(id, NLKind::UnqualifiedLookup, results);
  for (auto result0 : results) {
    if (auto result = dyn_cast<StructDecl>(result0)) {
      return result;;
    }
  }
  return nullptr;
}

Type deriveStructural_StructuralRepresentation(DerivedConformance &derived) {
  auto &C = derived.Context;
  auto type = derived.Nominal;

  ModuleDecl *structuralCoreDecl = C.getLoadedModule(C.Id_StructuralCore);
  StructDecl *structDecl = deriveStructural_lookupStructDecl(C, structuralCoreDecl, C.Id_Structural_Struct);
  StructDecl *propertyDecl = deriveStructural_lookupStructDecl(C, structuralCoreDecl, C.Id_Structural_Property);
  StructDecl *consDecl = deriveStructural_lookupStructDecl(C, structuralCoreDecl, C.Id_Structural_Cons);
  StructDecl *emptyDecl = deriveStructural_lookupStructDecl(C, structuralCoreDecl, C.Id_Structural_Empty);

  // Given property types [T1, ..., TN], compute the structural
  // representation as Cons<Property<T1>, ... Cons<Property<TN>, Empty> ... >>
  // type.
  Type propertiesType = emptyDecl->getDeclaredType();

  for (auto prop : reverse(type->getStoredProperties())) {
    auto propertyType = BoundGenericType::get(propertyDecl, Type(),
                                              {prop->getType()});
    propertiesType = BoundGenericType::get(consDecl, Type(),
                                           {propertyType, propertiesType});
  }

  // Wrap properties into the resulting Struct<Property<...>> type.
  Type structType = BoundGenericType::get(structDecl, Type(), {propertiesType});

  return structType;
}

static std::pair<BraceStmt *, bool>
deriveBodyStructural_init(AbstractFunctionDecl *initDecl, void *) {
  // The enclosing type decl.
  auto conformanceDC = initDecl->getDeclContext();
  auto *typeDecl = conformanceDC->getSelfNominalTypeDecl();

  auto *funcDC = cast<DeclContext>(initDecl);
  auto &C = funcDC->getASTContext();

  // Compute a constructor body that contains of a sequence of assignents
  // that extract the values out of the representation: 
  //
  //   {
  //      self.property1 = structuralRepresentation.properties.value.value
  //      self.property2 = structuralRepresentation.properties.next.value.value
  //      self.property3 = structuralRepresentation.properties.next.next.value.value
  //      ...
  //      self.propertyN = structuralRepresentation.properties.next.next. ... .value.value
  //   }
  //
  auto props = typeDecl->getStoredProperties();
  SmallVector<ASTNode, 4> stmts;
  if (props.size() > 0) {
    auto reprParam = initDecl->getParameters()->get(0);
    Expr *baseExpr = new (C)
        DeclRefExpr(ConcreteDeclRef(reprParam), DeclNameLoc(), /*Implicit=*/true);
    baseExpr = UnresolvedDotExpr::createImplicit(C, baseExpr, C.Id_properties);
    for (auto prop : props) {
      auto *selfRef = DerivedConformance::createSelfDeclRef(initDecl);
      auto *varExpr = UnresolvedDotExpr::createImplicit(C, selfRef,
                                                        prop->getName());
      auto *rhsExpr = baseExpr;
      rhsExpr = UnresolvedDotExpr::createImplicit(C, rhsExpr, C.Id_value);
      rhsExpr = UnresolvedDotExpr::createImplicit(C, rhsExpr, C.Id_value);
      baseExpr = UnresolvedDotExpr::createImplicit(C, baseExpr, C.Id_next);
      auto assign =
          new (C) AssignExpr(varExpr, SourceLoc(), rhsExpr, /*Implicit=*/true);
      stmts.push_back(assign);
    }
  }

  // Wrap the generate states into braces and return them as the result.
  auto body = BraceStmt::create(C, SourceLoc(), stmts, SourceLoc(),
                                /*implicit=*/true);

  return { body, /*isTypeChecked=*/ false };
}

ValueDecl *deriveStructural_init(DerivedConformance &derived) {
  auto &C = derived.Context;
  auto conformanceDC = derived.getConformanceContext();

  // Compute a representation type for Self.
  auto reprType = deriveStructural_StructuralRepresentation(derived);

  // Create a constructor parameter list for (structuralRepresentation: StructuralRepresentation).
  auto reprParamDecl =
      new (C) ParamDecl(SourceLoc(), SourceLoc(), C.Id_structuralRepresentation,
                        SourceLoc(), C.Id_structuralRepresentation, conformanceDC);
  reprParamDecl->setImplicit();
  reprParamDecl->setSpecifier(ParamSpecifier::Default);
  reprParamDecl->setInterfaceType(reprType);

  auto paramList = ParameterList::createWithoutLoc(reprParamDecl);

  // Create the declaration for the construtor.
  DeclName name(C, DeclBaseName::createConstructor(), paramList);

  auto *initDecl = new (C)
      ConstructorDecl(name, SourceLoc(),
                      /*Failable=*/false, /*FailabilityLoc=*/SourceLoc(),
                      /*Throws=*/false, /*ThrowsLoc=*/SourceLoc(), paramList,
                      /*GenericParams=*/nullptr, conformanceDC);
  initDecl->setImplicit();
  initDecl->setSynthesized();
  initDecl->setBodySynthesizer(&deriveBodyStructural_init);

  // Make sure to add the constructor to the derived members.
  derived.addMembersToConformanceContext({initDecl});

  return initDecl;
}

static std::pair<BraceStmt *, bool>
deriveBodyStructural_structuralRepresentation(AbstractFunctionDecl *getterDecl, void *) {
  // The enclosing type decl.
  auto conformanceDC = getterDecl->getDeclContext();
  auto *typeDecl = conformanceDC->getSelfNominalTypeDecl();

  auto *funcDC = cast<DeclContext>(getterDecl);
  auto &C = funcDC->getASTContext();

  // Look up StructuralCore module, and structs defined within it. 
  ModuleDecl *structuralCoreDecl = C.getLoadedModule(C.Id_StructuralCore);
  StructDecl *structDecl = deriveStructural_lookupStructDecl(C, structuralCoreDecl, C.Id_Structural_Struct);
  StructDecl *propertyDecl = deriveStructural_lookupStructDecl(C, structuralCoreDecl, C.Id_Structural_Property);
  StructDecl *consDecl = deriveStructural_lookupStructDecl(C, structuralCoreDecl, C.Id_Structural_Cons);
  StructDecl *emptyDecl = deriveStructural_lookupStructDecl(C, structuralCoreDecl, C.Id_Structural_Empty);

  // Compute the value for the struct properties as:
  //
  //   Cons(Property(self.property1), ... Cons(Property(self.propertyN), Empty()) ... )
  //
  auto emptyRef =  new (C) DeclRefExpr(ConcreteDeclRef(emptyDecl), DeclNameLoc(), /*Implicit=*/true);
  auto emptyCall = CallExpr::createImplicit(C, emptyRef, {}, {});
  Expr *propertiesExpr = emptyCall;

  for (auto prop : reverse(typeDecl->getStoredProperties())) {
    auto *selfRef = DerivedConformance::createSelfDeclRef(getterDecl);
    auto *varExpr = UnresolvedDotExpr::createImplicit(C, selfRef,
                                                      prop->getName());
    auto propertyRef = new (C) DeclRefExpr(ConcreteDeclRef(propertyDecl), DeclNameLoc(), /*Implicit=*/true);
    auto propertyExpr = CallExpr::createImplicit(C, propertyRef, {varExpr}, {});
    auto consRef = new (C) DeclRefExpr(ConcreteDeclRef(consDecl), DeclNameLoc(), /*Implicit=*/true);
    propertiesExpr = CallExpr::createImplicit(C, consRef, {propertyExpr, propertiesExpr}, {});
  }

  // Compute the body of the computed property as:
  //
  //   {
  //     return Struct(Cons(...))
  //   }
  //
  auto structRef = new (C) DeclRefExpr(ConcreteDeclRef(structDecl), DeclNameLoc(), /*Implicit=*/true);
  Expr *retValue = CallExpr::createImplicit(C, structRef, {propertiesExpr}, {});

  auto retStmt = new (C) ReturnStmt(SourceLoc(), retValue, /*implicit=*/true);

  auto body = BraceStmt::create(C, SourceLoc(), {retStmt}, SourceLoc(),
                                /*implicit=*/true);

  return { body, /*isTypeChecked=*/ false };
}

ValueDecl *deriveStructural_structuralRepresentation(DerivedConformance &derived) {
  auto &C = derived.Context;
  auto conformanceDC = derived.getConformanceContext();

  // Compute a structural representation of Self.
  auto reprType = deriveStructural_StructuralRepresentation(derived);

  // Create declaration for computed property.
  VarDecl *var = new (C) VarDecl(/*IsStatic*/ false, VarDecl::Introducer::Var,
                                   /*IsCaptureList*/ false, SourceLoc(),
                                   C.Id_structuralRepresentation, conformanceDC);
  var->setInterfaceType(reprType);

  // Create an accessor for the computed property.
  AccessorDecl *getter = AccessorDecl::create(
      C, /*FuncLoc=*/SourceLoc(), /*AccessorKeywordLoc=*/SourceLoc(),
      AccessorKind::Get, var,
      /*StaticLoc=*/SourceLoc(), StaticSpellingKind::None,
      /*Throws=*/false, /*ThrowsLoc=*/SourceLoc(),
      /*GenericParams=*/nullptr, ParameterList::createEmpty(C),
      TypeLoc::withoutLoc(reprType), conformanceDC);
  getter->setImplicit();
  getter->setSynthesized();
  getter->setBodySynthesizer(deriveBodyStructural_structuralRepresentation);

  var->setImplicit();
  var->copyFormalAccessFrom(derived.Nominal, /*sourceIsParentContext*/ true);
  var->setImplInfo(StorageImplInfo::getImmutableComputed());
  var->setAccessors(SourceLoc(), {getter}, SourceLoc());

  // Create a pattern declaration for the computed property. 
  Pattern *internalPat = NamedPattern::createImplicit(C, var);
  internalPat->setType(reprType);
  internalPat = TypedPattern::createImplicit(C, internalPat, reprType);
  internalPat->setType(reprType);
  auto *pat = PatternBindingDecl::createImplicit(
      C, StaticSpellingKind::None, internalPat, /*InitExpr*/ nullptr, conformanceDC);

  // Make sure to add the computed property and pattern declaration to the derived members.
  derived.addMembersToConformanceContext({var, pat});

  return var;
}

} // namespace

bool DerivedConformance::canDeriveStructural(NominalTypeDecl *type) {
  return true;
}

Type DerivedConformance::deriveStructural(AssociatedTypeDecl *requirement) {
  if (checkAndDiagnoseDisallowedContext(requirement))
    return nullptr;

  if (!canDeriveStructural(Nominal))
    return nullptr;

  if (requirement->getName() == Context.Id_StructuralRepresentation) {
    return deriveStructural_StructuralRepresentation(*this);
  }

  return nullptr;
}

ValueDecl *DerivedConformance::deriveStructural(ValueDecl *requirement) {
  if (checkAndDiagnoseDisallowedContext(requirement))
    return nullptr;

  if (!canDeriveStructural(Nominal))
    return nullptr;

  if (isa<ConstructorDecl>(requirement)) {
    return deriveStructural_init(*this);
  }

  if (requirement->getBaseName() == Context.Id_structuralRepresentation) {
    return deriveStructural_structuralRepresentation(*this);
  }

  return nullptr;
}
