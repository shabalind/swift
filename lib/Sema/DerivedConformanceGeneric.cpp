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

StructDecl *deriveGeneric_lookupStructDecl(swift::ASTContext &ctx, 
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

ArrayRef<Type> deriveGeneric_collectPropertyTypesInReverse(DerivedConformance &derived) {
  SmallVector<Type, 4> propTypesImpl;
  for (auto prop : derived.Nominal->getStoredProperties()) {
    propTypesImpl.push_back(prop->getType());
  }
  ArrayRef<Type> propTypes = propTypesImpl;
  return propTypes;
}

Type deriveGeneric_Representation(DerivedConformance &derived) {
  auto &ctx = derived.Context;

  ModuleDecl *genericCoreDecl = ctx.getLoadedModule(ctx.Id_GenericCore);
  StructDecl *structDecl = deriveGeneric_lookupStructDecl(ctx, genericCoreDecl, ctx.Id_Struct);
  StructDecl *fieldDecl = deriveGeneric_lookupStructDecl(ctx, genericCoreDecl, ctx.Id_Field);
  StructDecl *emptyDecl = deriveGeneric_lookupStructDecl(ctx, genericCoreDecl, ctx.Id_Empty);

  // Collect stored property types in reverse order [TN, ..., T1]
  auto propTypes = deriveGeneric_collectPropertyTypesInReverse(derived);

  // Compute Field<T1, Field<T2, ... <Field<TN, Empty>>>> type.
  Type fieldsType = emptyDecl->getDeclaredType();

  while (propTypes.size() > 0) {
    fieldsType = BoundGenericType::get(fieldDecl, Type(),
                                        {propTypes.back(), fieldsType});
    propTypes = propTypes.drop_back(1);
  }

  // Wrap fields into the resulting Struct<Field<...>> type.
  Type structType = BoundGenericType::get(structDecl, Type(), {fieldsType});

  return structType;
}

ValueDecl *deriveGeneric_init(DerivedConformance &derived) {
  auto &ctx = derived.Context;
  auto type = derived.Nominal;

  // Create a constructor parameter list for (representation: Representation)
  auto param =
      new (ctx) ParamDecl(SourceLoc(), SourceLoc(), ctx.Id_representation,
                          SourceLoc(), ctx.Id_representation, type);
  param->setSpecifier(ParamSpecifier::Default);
  param->setInterfaceType(deriveGeneric_Representation(derived));
  auto paramList = ParameterList::create(ctx, param);

  // Compute a constructor body that contains of a sequence of assignents
  // that extract the values out of the representation: 
  //
  //   {
  //      self.field1 = representation.value
  //      self.field2 = representation.next.value
  //      self.field3 = representation.next.next.value
  //      ...
  //      self.fieldN = representation.next.next. ... .value
  //   }
  //
  auto props = type->getStoredProperties();
  SmallVector<ASTNode, 4> stmts;
  if (props.size() > 0) {
    Expr *base = new (ctx)
        DeclRefExpr(ConcreteDeclRef(param), DeclNameLoc(), /*Implicit=*/true);
    for (auto prop : props) {
      auto lhs = UnresolvedDeclRefExpr::createImplicit(ctx, prop->getName());
      Expr *rhs;
      if (prop != type->getStoredProperties().back()) {
        rhs = UnresolvedDotExpr::createImplicit(ctx, base, ctx.Id_value);
        base = UnresolvedDotExpr::createImplicit(ctx, base, ctx.Id_next);
      } else {
        rhs = base;
      }
      auto assign =
          new (ctx) AssignExpr(lhs, SourceLoc(), rhs, /*Implicit=*/true);
      stmts.push_back(assign);
    }
  }
  auto body = BraceStmt::create(ctx, SourceLoc(), stmts, SourceLoc(),
                                /*implicit=*/true);

  // Create the declaration for the construtor.
  DeclName name(ctx, DeclBaseName::createConstructor(), paramList);
  auto *ctor = new (ctx)
      ConstructorDecl(name, type->getLoc(),
                      /*Failable=*/false, /*FailabilityLoc=*/SourceLoc(),
                      /*Throws=*/false, /*ThrowsLoc=*/SourceLoc(), paramList,
                      /*GenericParams=*/nullptr, type);
  ctor->setImplicit();
  ctor->copyFormalAccessFrom(type, /*sourceIsParentContext*/ true);
  ctor->setBody(body);

  // Make sure to add the constructor to the derived members.
  derived.addMembersToConformanceContext({ctor});

  return ctor;
}

ValueDecl *deriveGeneric_representation(DerivedConformance &derived) {
  auto &ctx = derived.Context;
  auto type = derived.Nominal;
  auto ret = deriveGeneric_Representation(derived);

  auto props = type->getStoredProperties();
  Expr *result;
  SmallVector<ASTNode, 4> stmts;
  if (props.size() == 0) {
    result = TupleExpr::createEmpty(ctx, SourceLoc(), SourceLoc(),
                                    /*Implicit=*/true);
  } else {
    result =
        UnresolvedDeclRefExpr::createImplicit(ctx, props.back()->getName());
    for (auto prop : reverse(props.drop_back(1))) {
      auto product = UnresolvedDeclRefExpr::createImplicit(ctx, ctx.Id_Product);
      auto value = UnresolvedDeclRefExpr::createImplicit(ctx, prop->getName());
      result = CallExpr::createImplicit(ctx, product, {value, result}, {});
    }
  }
  auto stmt = new (ctx) ReturnStmt(SourceLoc(), result, /*implicit=*/true);
  auto body = BraceStmt::create(ctx, SourceLoc(), {stmt}, SourceLoc(),
                                /*implicit=*/true);

  VarDecl *var = new (ctx) VarDecl(/*IsStatic*/ false, VarDecl::Introducer::Var,
                                   /*IsCaptureList*/ false, SourceLoc(),
                                   ctx.Id_representation, type);
  var->setInterfaceType(ret);

  AccessorDecl *getter = AccessorDecl::create(
      ctx, /*FuncLoc=*/SourceLoc(), /*AccessorKeywordLoc=*/SourceLoc(),
      AccessorKind::Get, var,
      /*StaticLoc=*/SourceLoc(), StaticSpellingKind::None,
      /*Throws=*/false, /*ThrowsLoc=*/SourceLoc(),
      /*GenericParams=*/nullptr, ParameterList::createEmpty(ctx),
      TypeLoc::withoutLoc(ret), type);
  getter->setImplicit();
  getter->copyFormalAccessFrom(derived.Nominal, /*sourceIsParentContext*/ true);
  getter->setBody(body);

  var->setImplicit();
  var->copyFormalAccessFrom(derived.Nominal, /*sourceIsParentContext*/ true);
  var->setImplInfo(StorageImplInfo::getImmutableComputed());
  var->setAccessors(SourceLoc(), {getter}, SourceLoc());

  Pattern *internalPat = NamedPattern::createImplicit(ctx, var);
  internalPat->setType(ret);
  internalPat = TypedPattern::createImplicit(ctx, internalPat, ret);
  internalPat->setType(ret);
  auto *pat = PatternBindingDecl::createImplicit(
      ctx, StaticSpellingKind::None, internalPat, /*InitExpr*/ nullptr, type);

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
