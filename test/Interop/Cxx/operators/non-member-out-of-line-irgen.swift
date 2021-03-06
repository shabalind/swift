// RUN: %target-swift-emit-ir %s -I %S/Inputs -enable-cxx-interop | %FileCheck %s

import NonMemberOutOfLine

public func add(_ lhs: IntBox, _ rhs: IntBox) -> IntBox { lhs + rhs }

// CHECK: call i32 [[NAME:@(_Zpl6IntBoxS_|"\?\?H@YA\?AUIntBox@@U0@0@Z")]](i32 %{{[0-9]+}}, i32 %{{[0-9]+}})
// CHECK: declare {{(dso_local )?}}i32 [[NAME]](i32, i32)
