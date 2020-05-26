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

StructDecl *deriveGeneric_lookupStructDecl(swift::ASTContext &C, 
                                           ModuleDecl *genericCoreDecl,
                                           swift::Identifier id) {
  SmallVector<ValueDecl *, 1> results;
  genericCoreDecl->lookupValue(id, NLKind::UnqualifiedLookup, results);
  for (auto result0 : results) {
    if (auto result = dyn_cast<StructDecl>(result0)) {
      return result;;
    }
  }
  return nullptr;
}

Type deriveGeneric_Representation(DerivedConformance &derived) {
  auto &C = derived.Context;
  auto type = derived.Nominal;

  ModuleDecl *genericCoreDecl = C.getLoadedModule(C.Id_GenericCore);
  StructDecl *structDecl = deriveGeneric_lookupStructDecl(C, genericCoreDecl, C.Id_Struct);
  StructDecl *fieldDecl = deriveGeneric_lookupStructDecl(C, genericCoreDecl, C.Id_Field);
  StructDecl *emptyDecl = deriveGeneric_lookupStructDecl(C, genericCoreDecl, C.Id_Empty);

  // Compute Field<T1, Field<T2, ... <Field<TN, Empty>> ... >> type.
  Type fieldsType = emptyDecl->getDeclaredType();

  for (auto prop : reverse(type->getStoredProperties())) {
    auto propType = prop->getType();
    fieldsType = BoundGenericType::get(fieldDecl, Type(),
                                       {propType, fieldsType});
  }

  // Wrap fields into the resulting Struct<Field<...>> type.
  Type structType = BoundGenericType::get(structDecl, Type(), {fieldsType});

  return structType;
}

static std::pair<BraceStmt *, bool>
deriveBodyGeneric_init(AbstractFunctionDecl *initDecl, void *) {
  // The enclosing type decl.
  auto conformanceDC = initDecl->getDeclContext();
  auto *typeDecl = conformanceDC->getSelfNominalTypeDecl();

  auto *funcDC = cast<DeclContext>(initDecl);
  auto &C = funcDC->getASTContext();

  // Compute a constructor body that contains of a sequence of assignents
  // that extract the values out of the representation: 
  //
  //   {
  //      self.field1 = representation.shape.value
  //      self.field2 = representation.shape.next.value
  //      self.field3 = representation.shape.next.next.value
  //      ...
  //      self.fieldN = representation.shape.next.next. ... .value
  //   }
  //
  auto props = typeDecl->getStoredProperties();
  SmallVector<ASTNode, 4> stmts;
  if (props.size() > 0) {
    auto reprParam = initDecl->getParameters()->get(0);
    Expr *baseExpr = new (C)
        DeclRefExpr(ConcreteDeclRef(reprParam), DeclNameLoc(), /*Implicit=*/true);
    baseExpr = UnresolvedDotExpr::createImplicit(C, baseExpr, C.Id_shape);
    for (auto prop : props) {
      auto *selfRef = DerivedConformance::createSelfDeclRef(initDecl);
      auto *varExpr = UnresolvedDotExpr::createImplicit(C, selfRef,
                                                        prop->getName());
      Expr *rhsExpr = UnresolvedDotExpr::createImplicit(C, baseExpr, C.Id_value);
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

ValueDecl *deriveGeneric_init(DerivedConformance &derived) {
  auto &C = derived.Context;
  auto conformanceDC = derived.getConformanceContext();

  // Compute a representation type for Self.
  auto reprType = deriveGeneric_Representation(derived);

  // Create a constructor parameter list for (representation: Representation)
  auto reprParamDecl =
      new (C) ParamDecl(SourceLoc(), SourceLoc(), C.Id_representation,
                        SourceLoc(), C.Id_representation, conformanceDC);
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
  initDecl->setBodySynthesizer(&deriveBodyGeneric_init);

  // Make sure to add the constructor to the derived members.
  derived.addMembersToConformanceContext({initDecl});

  return initDecl;
}

static std::pair<BraceStmt *, bool>
deriveBodyGeneric_representation(AbstractFunctionDecl *getterDecl, void *) {
  // The enclosing type decl.
  auto conformanceDC = getterDecl->getDeclContext();
  auto *typeDecl = conformanceDC->getSelfNominalTypeDecl();

  auto *funcDC = cast<DeclContext>(getterDecl);
  auto &C = funcDC->getASTContext();

  // Look up GenericCore module, and structs defined within it. 
  ModuleDecl *genericCoreDecl = C.getLoadedModule(C.Id_GenericCore);
  StructDecl *structDecl = deriveGeneric_lookupStructDecl(C, genericCoreDecl, C.Id_Struct);
  StructDecl *fieldDecl = deriveGeneric_lookupStructDecl(C, genericCoreDecl, C.Id_Field);
  StructDecl *emptyDecl = deriveGeneric_lookupStructDecl(C, genericCoreDecl, C.Id_Empty);

  // Compute the value for the struct fields as:
  //
  //   Field(self.field1, ... Field(self.fieldN, Empty()) ... )
  //
  auto emptyRef =  new (C) DeclRefExpr(ConcreteDeclRef(emptyDecl), DeclNameLoc(), /*Implicit=*/true);
  auto emptyCall = CallExpr::createImplicit(C, emptyRef, {}, {});
  Expr *fieldsExpr = emptyCall;

  for (auto prop : reverse(typeDecl->getStoredProperties())) {
    auto *selfRef = DerivedConformance::createSelfDeclRef(getterDecl);
    auto *varExpr = UnresolvedDotExpr::createImplicit(C, selfRef,
                                                      prop->getName());
    auto fieldRef = new (C) DeclRefExpr(ConcreteDeclRef(fieldDecl), DeclNameLoc(), /*Implicit=*/true);
    fieldsExpr = CallExpr::createImplicit(C, fieldRef, {varExpr, fieldsExpr}, {});
  }

  // Compute the body of the computed property as:
  //
  //   {
  //     return Struct(Field(...))
  //   }
  //
  auto structRef = new (C) DeclRefExpr(ConcreteDeclRef(structDecl), DeclNameLoc(), /*Implicit=*/true);
  Expr *retValue = CallExpr::createImplicit(C, structRef, {fieldsExpr}, {});

  auto retStmt = new (C) ReturnStmt(SourceLoc(), retValue, /*implicit=*/true);

  auto body = BraceStmt::create(C, SourceLoc(), {retStmt}, SourceLoc(),
                                /*implicit=*/true);

  return { body, /*isTypeChecked=*/ false };
}

ValueDecl *deriveGeneric_representation(DerivedConformance &derived) {
  auto &C = derived.Context;
  auto conformanceDC = derived.getConformanceContext();

  // Compute a representation type for Self.
  auto reprType = deriveGeneric_Representation(derived);

  // Create declaration for computed property.
  VarDecl *var = new (C) VarDecl(/*IsStatic*/ false, VarDecl::Introducer::Var,
                                   /*IsCaptureList*/ false, SourceLoc(),
                                   C.Id_representation, conformanceDC);
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
  getter->setBodySynthesizer(deriveBodyGeneric_representation);

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

bool DerivedConformance::canDeriveGeneric(NominalTypeDecl *type) {
  return true;
}

Type DerivedConformance::deriveGeneric(AssociatedTypeDecl *requirement) {
  if (checkAndDiagnoseDisallowedContext(requirement))
    return nullptr;

  if (!canDeriveGeneric(Nominal))
    return nullptr;

  if (requirement->getName() == Context.Id_Representation) {
    return deriveGeneric_Representation(*this);
  }

  return nullptr;
}

ValueDecl *DerivedConformance::deriveGeneric(ValueDecl *requirement) {
  if (checkAndDiagnoseDisallowedContext(requirement))
    return nullptr;

  if (!canDeriveGeneric(Nominal))
    return nullptr;

  if (isa<ConstructorDecl>(requirement)) {
    return deriveGeneric_init(*this);
  }

  if (requirement->getBaseName() == Context.Id_representation) {
    return deriveGeneric_representation(*this);
  }

  return nullptr;
}
