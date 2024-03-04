
// ** Expanded prelude

// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

// Basic theory for vectors using arrays. This version of vectors is not extensional.

datatype Vec<T> {
    Vec(v: [int]T, l: int)
}

function {:builtin "MapConst"} MapConstVec<T>(T): [int]T;
function DefaultVecElem<T>(): T;
function {:inline} DefaultVecMap<T>(): [int]T { MapConstVec(DefaultVecElem()) }

function {:inline} EmptyVec<T>(): Vec T {
    Vec(DefaultVecMap(), 0)
}

function {:inline} MakeVec1<T>(v: T): Vec T {
    Vec(DefaultVecMap()[0 := v], 1)
}

function {:inline} MakeVec2<T>(v1: T, v2: T): Vec T {
    Vec(DefaultVecMap()[0 := v1][1 := v2], 2)
}

function {:inline} MakeVec3<T>(v1: T, v2: T, v3: T): Vec T {
    Vec(DefaultVecMap()[0 := v1][1 := v2][2 := v3], 3)
}

function {:inline} MakeVec4<T>(v1: T, v2: T, v3: T, v4: T): Vec T {
    Vec(DefaultVecMap()[0 := v1][1 := v2][2 := v3][3 := v4], 4)
}

function {:inline} ExtendVec<T>(v: Vec T, elem: T): Vec T {
    (var l := v->l;
    Vec(v->v[l := elem], l + 1))
}

function {:inline} ReadVec<T>(v: Vec T, i: int): T {
    v->v[i]
}

function {:inline} LenVec<T>(v: Vec T): int {
    v->l
}

function {:inline} IsEmptyVec<T>(v: Vec T): bool {
    v->l == 0
}

function {:inline} RemoveVec<T>(v: Vec T): Vec T {
    (var l := v->l - 1;
    Vec(v->v[l := DefaultVecElem()], l))
}

function {:inline} RemoveAtVec<T>(v: Vec T, i: int): Vec T {
    (var l := v->l - 1;
    Vec(
        (lambda j: int ::
           if j >= 0 && j < l then
               if j < i then v->v[j] else v->v[j+1]
           else DefaultVecElem()),
        l))
}

function {:inline} ConcatVec<T>(v1: Vec T, v2: Vec T): Vec T {
    (var l1, m1, l2, m2 := v1->l, v1->v, v2->l, v2->v;
    Vec(
        (lambda i: int ::
          if i >= 0 && i < l1 + l2 then
            if i < l1 then m1[i] else m2[i - l1]
          else DefaultVecElem()),
        l1 + l2))
}

function {:inline} ReverseVec<T>(v: Vec T): Vec T {
    (var l := v->l;
    Vec(
        (lambda i: int :: if 0 <= i && i < l then v->v[l - i - 1] else DefaultVecElem()),
        l))
}

function {:inline} SliceVec<T>(v: Vec T, i: int, j: int): Vec T {
    (var m := v->v;
    Vec(
        (lambda k:int ::
          if 0 <= k && k < j - i then
            m[i + k]
          else
            DefaultVecElem()),
        (if j - i < 0 then 0 else j - i)))
}


function {:inline} UpdateVec<T>(v: Vec T, i: int, elem: T): Vec T {
    Vec(v->v[i := elem], v->l)
}

function {:inline} SwapVec<T>(v: Vec T, i: int, j: int): Vec T {
    (var m := v->v;
    Vec(m[i := m[j]][j := m[i]], v->l))
}

function {:inline} ContainsVec<T>(v: Vec T, e: T): bool {
    (var l := v->l;
    (exists i: int :: InRangeVec(v, i) && v->v[i] == e))
}

function IndexOfVec<T>(v: Vec T, e: T): int;
axiom {:ctor "Vec"} (forall<T> v: Vec T, e: T :: {IndexOfVec(v, e)}
    (var i := IndexOfVec(v,e);
     if (!ContainsVec(v, e)) then i == -1
     else InRangeVec(v, i) && ReadVec(v, i) == e &&
        (forall j: int :: j >= 0 && j < i ==> ReadVec(v, j) != e)));

// This function should stay non-inlined as it guards many quantifiers
// over vectors. It appears important to have this uninterpreted for
// quantifier triggering.
function InRangeVec<T>(v: Vec T, i: int): bool {
    i >= 0 && i < LenVec(v)
}

// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

// Boogie model for multisets, based on Boogie arrays. This theory assumes extensional equality for element types.

datatype Multiset<T> {
    Multiset(v: [T]int, l: int)
}

function {:builtin "MapConst"} MapConstMultiset<T>(l: int): [T]int;

function {:inline} EmptyMultiset<T>(): Multiset T {
    Multiset(MapConstMultiset(0), 0)
}

function {:inline} LenMultiset<T>(s: Multiset T): int {
    s->l
}

function {:inline} ExtendMultiset<T>(s: Multiset T, v: T): Multiset T {
    (var len := s->l;
    (var cnt := s->v[v];
    Multiset(s->v[v := (cnt + 1)], len + 1)))
}

// This function returns (s1 - s2). This function assumes that s2 is a subset of s1.
function {:inline} SubtractMultiset<T>(s1: Multiset T, s2: Multiset T): Multiset T {
    (var len1 := s1->l;
    (var len2 := s2->l;
    Multiset((lambda v:T :: s1->v[v]-s2->v[v]), len1-len2)))
}

function {:inline} IsEmptyMultiset<T>(s: Multiset T): bool {
    (s->l == 0) &&
    (forall v: T :: s->v[v] == 0)
}

function {:inline} IsSubsetMultiset<T>(s1: Multiset T, s2: Multiset T): bool {
    (s1->l <= s2->l) &&
    (forall v: T :: s1->v[v] <= s2->v[v])
}

function {:inline} ContainsMultiset<T>(s: Multiset T, v: T): bool {
    s->v[v] > 0
}

// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

// Theory for tables.

// v is the SMT array holding the key-value assignment. e is an array which
// independently determines whether a key is valid or not. l is the length.
//
// Note that even though the program cannot reflect over existence of a key,
// we want the specification to be able to do this, so it can express
// verification conditions like "key has been inserted".
datatype Table <K, V> {
    Table(v: [K]V, e: [K]bool, l: int)
}

// Functions for default SMT arrays. For the table values, we don't care and
// use an uninterpreted function.
function DefaultTableArray<K, V>(): [K]V;
function DefaultTableKeyExistsArray<K>(): [K]bool;
axiom DefaultTableKeyExistsArray() == (lambda i: int :: false);

function {:inline} EmptyTable<K, V>(): Table K V {
    Table(DefaultTableArray(), DefaultTableKeyExistsArray(), 0)
}

function {:inline} GetTable<K,V>(t: Table K V, k: K): V {
    // Notice we do not check whether key is in the table. The result is undetermined if it is not.
    t->v[k]
}

function {:inline} LenTable<K,V>(t: Table K V): int {
    t->l
}


function {:inline} ContainsTable<K,V>(t: Table K V, k: K): bool {
    t->e[k]
}

function {:inline} UpdateTable<K,V>(t: Table K V, k: K, v: V): Table K V {
    Table(t->v[k := v], t->e, t->l)
}

function {:inline} AddTable<K,V>(t: Table K V, k: K, v: V): Table K V {
    // This function has an undetermined result if the key is already in the table
    // (all specification functions have this "partial definiteness" behavior). Thus we can
    // just increment the length.
    Table(t->v[k := v], t->e[k := true], t->l + 1)
}

function {:inline} RemoveTable<K,V>(t: Table K V, k: K): Table K V {
    // Similar as above, we only need to consider the case where the key is in the table.
    Table(t->v, t->e[k := false], t->l - 1)
}

axiom {:ctor "Table"} (forall<K,V> t: Table K V :: {LenTable(t)}
    (exists k: K :: {ContainsTable(t, k)} ContainsTable(t, k)) ==> LenTable(t) >= 1
);
// TODO: we might want to encoder a stronger property that the length of table
// must be more than N given a set of N items. Currently we don't see a need here
// and the above axiom seems to be sufficient.
// Copyright © Aptos Foundation
// SPDX-License-Identifier: Apache-2.0

// ==================================================================================
// Native object::exists_at

// ==================================================================================
// Intrinsic implementation of aggregator and aggregator factory

datatype $1_aggregator_Aggregator {
    $1_aggregator_Aggregator($handle: int, $key: int, $limit: int, $val: int)
}
function {:inline} $Update'$1_aggregator_Aggregator'_handle(s: $1_aggregator_Aggregator, x: int): $1_aggregator_Aggregator {
    $1_aggregator_Aggregator(x, s->$key, s->$limit, s->$val)
}
function {:inline} $Update'$1_aggregator_Aggregator'_key(s: $1_aggregator_Aggregator, x: int): $1_aggregator_Aggregator {
    $1_aggregator_Aggregator(s->$handle, x, s->$limit, s->$val)
}
function {:inline} $Update'$1_aggregator_Aggregator'_limit(s: $1_aggregator_Aggregator, x: int): $1_aggregator_Aggregator {
    $1_aggregator_Aggregator(s->$handle, s->$key, x, s->$val)
}
function {:inline} $Update'$1_aggregator_Aggregator'_val(s: $1_aggregator_Aggregator, x: int): $1_aggregator_Aggregator {
    $1_aggregator_Aggregator(s->$handle, s->$key, s->$limit, x)
}
function $IsValid'$1_aggregator_Aggregator'(s: $1_aggregator_Aggregator): bool {
    $IsValid'address'(s->$handle)
      && $IsValid'address'(s->$key)
      && $IsValid'u128'(s->$limit)
      && $IsValid'u128'(s->$val)
}
function {:inline} $IsEqual'$1_aggregator_Aggregator'(s1: $1_aggregator_Aggregator, s2: $1_aggregator_Aggregator): bool {
    s1 == s2
}
function {:inline} $1_aggregator_spec_get_limit(s: $1_aggregator_Aggregator): int {
    s->$limit
}
function {:inline} $1_aggregator_spec_get_handle(s: $1_aggregator_Aggregator): int {
    s->$handle
}
function {:inline} $1_aggregator_spec_get_key(s: $1_aggregator_Aggregator): int {
    s->$key
}
function {:inline} $1_aggregator_spec_get_val(s: $1_aggregator_Aggregator): int {
    s->$val
}

function $1_aggregator_spec_read(agg: $1_aggregator_Aggregator): int {
    $1_aggregator_spec_get_val(agg)
}

function $1_aggregator_spec_aggregator_set_val(agg: $1_aggregator_Aggregator, val: int): $1_aggregator_Aggregator {
    $Update'$1_aggregator_Aggregator'_val(agg, val)
}

function $1_aggregator_spec_aggregator_get_val(agg: $1_aggregator_Aggregator): int {
    $1_aggregator_spec_get_val(agg)
}

function $1_aggregator_factory_spec_new_aggregator(limit: int) : $1_aggregator_Aggregator;

axiom (forall limit: int :: {$1_aggregator_factory_spec_new_aggregator(limit)}
    (var agg := $1_aggregator_factory_spec_new_aggregator(limit);
     $1_aggregator_spec_get_limit(agg) == limit));

axiom (forall limit: int :: {$1_aggregator_factory_spec_new_aggregator(limit)}
     (var agg := $1_aggregator_factory_spec_new_aggregator(limit);
     $1_aggregator_spec_aggregator_get_val(agg) == 0));


// ============================================================================================
// Primitive Types

const $MAX_U8: int;
axiom $MAX_U8 == 255;
const $MAX_U16: int;
axiom $MAX_U16 == 65535;
const $MAX_U32: int;
axiom $MAX_U32 == 4294967295;
const $MAX_U64: int;
axiom $MAX_U64 == 18446744073709551615;
const $MAX_U128: int;
axiom $MAX_U128 == 340282366920938463463374607431768211455;
const $MAX_U256: int;
axiom $MAX_U256 == 115792089237316195423570985008687907853269984665640564039457584007913129639935;

// Templates for bitvector operations

function {:bvbuiltin "bvand"} $And'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvor"} $Or'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvxor"} $Xor'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvadd"} $Add'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvsub"} $Sub'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvmul"} $Mul'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvudiv"} $Div'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvurem"} $Mod'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvshl"} $Shl'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvlshr"} $Shr'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvult"} $Lt'Bv8'(bv8,bv8) returns(bool);
function {:bvbuiltin "bvule"} $Le'Bv8'(bv8,bv8) returns(bool);
function {:bvbuiltin "bvugt"} $Gt'Bv8'(bv8,bv8) returns(bool);
function {:bvbuiltin "bvuge"} $Ge'Bv8'(bv8,bv8) returns(bool);

procedure {:inline 1} $AddBv8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    if ($Lt'Bv8'($Add'Bv8'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Add'Bv8'(src1, src2);
}

procedure {:inline 1} $AddBv8_unchecked(src1: bv8, src2: bv8) returns (dst: bv8)
{
    dst := $Add'Bv8'(src1, src2);
}

procedure {:inline 1} $SubBv8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    if ($Lt'Bv8'(src1, src2)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Sub'Bv8'(src1, src2);
}

procedure {:inline 1} $MulBv8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    if ($Lt'Bv8'($Mul'Bv8'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mul'Bv8'(src1, src2);
}

procedure {:inline 1} $DivBv8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    if (src2 == 0bv8) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Div'Bv8'(src1, src2);
}

procedure {:inline 1} $ModBv8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    if (src2 == 0bv8) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mod'Bv8'(src1, src2);
}

procedure {:inline 1} $AndBv8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    dst := $And'Bv8'(src1,src2);
}

procedure {:inline 1} $OrBv8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    dst := $Or'Bv8'(src1,src2);
}

procedure {:inline 1} $XorBv8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    dst := $Xor'Bv8'(src1,src2);
}

procedure {:inline 1} $LtBv8(src1: bv8, src2: bv8) returns (dst: bool)
{
    dst := $Lt'Bv8'(src1,src2);
}

procedure {:inline 1} $LeBv8(src1: bv8, src2: bv8) returns (dst: bool)
{
    dst := $Le'Bv8'(src1,src2);
}

procedure {:inline 1} $GtBv8(src1: bv8, src2: bv8) returns (dst: bool)
{
    dst := $Gt'Bv8'(src1,src2);
}

procedure {:inline 1} $GeBv8(src1: bv8, src2: bv8) returns (dst: bool)
{
    dst := $Ge'Bv8'(src1,src2);
}

function $IsValid'bv8'(v: bv8): bool {
  $Ge'Bv8'(v,0bv8) && $Le'Bv8'(v,255bv8)
}

function {:inline} $IsEqual'bv8'(x: bv8, y: bv8): bool {
    x == y
}

procedure {:inline 1} $int2bv8(src: int) returns (dst: bv8)
{
    if (src > 255) {
        call $ExecFailureAbort();
        return;
    }
    dst := $int2bv.8(src);
}

procedure {:inline 1} $bv2int8(src: bv8) returns (dst: int)
{
    dst := $bv2int.8(src);
}

function {:builtin "(_ int2bv 8)"} $int2bv.8(i: int) returns (bv8);
function {:builtin "bv2nat"} $bv2int.8(i: bv8) returns (int);

function {:bvbuiltin "bvand"} $And'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvor"} $Or'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvxor"} $Xor'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvadd"} $Add'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvsub"} $Sub'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvmul"} $Mul'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvudiv"} $Div'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvurem"} $Mod'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvshl"} $Shl'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvlshr"} $Shr'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvult"} $Lt'Bv16'(bv16,bv16) returns(bool);
function {:bvbuiltin "bvule"} $Le'Bv16'(bv16,bv16) returns(bool);
function {:bvbuiltin "bvugt"} $Gt'Bv16'(bv16,bv16) returns(bool);
function {:bvbuiltin "bvuge"} $Ge'Bv16'(bv16,bv16) returns(bool);

procedure {:inline 1} $AddBv16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    if ($Lt'Bv16'($Add'Bv16'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Add'Bv16'(src1, src2);
}

procedure {:inline 1} $AddBv16_unchecked(src1: bv16, src2: bv16) returns (dst: bv16)
{
    dst := $Add'Bv16'(src1, src2);
}

procedure {:inline 1} $SubBv16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    if ($Lt'Bv16'(src1, src2)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Sub'Bv16'(src1, src2);
}

procedure {:inline 1} $MulBv16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    if ($Lt'Bv16'($Mul'Bv16'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mul'Bv16'(src1, src2);
}

procedure {:inline 1} $DivBv16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    if (src2 == 0bv16) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Div'Bv16'(src1, src2);
}

procedure {:inline 1} $ModBv16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    if (src2 == 0bv16) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mod'Bv16'(src1, src2);
}

procedure {:inline 1} $AndBv16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    dst := $And'Bv16'(src1,src2);
}

procedure {:inline 1} $OrBv16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    dst := $Or'Bv16'(src1,src2);
}

procedure {:inline 1} $XorBv16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    dst := $Xor'Bv16'(src1,src2);
}

procedure {:inline 1} $LtBv16(src1: bv16, src2: bv16) returns (dst: bool)
{
    dst := $Lt'Bv16'(src1,src2);
}

procedure {:inline 1} $LeBv16(src1: bv16, src2: bv16) returns (dst: bool)
{
    dst := $Le'Bv16'(src1,src2);
}

procedure {:inline 1} $GtBv16(src1: bv16, src2: bv16) returns (dst: bool)
{
    dst := $Gt'Bv16'(src1,src2);
}

procedure {:inline 1} $GeBv16(src1: bv16, src2: bv16) returns (dst: bool)
{
    dst := $Ge'Bv16'(src1,src2);
}

function $IsValid'bv16'(v: bv16): bool {
  $Ge'Bv16'(v,0bv16) && $Le'Bv16'(v,65535bv16)
}

function {:inline} $IsEqual'bv16'(x: bv16, y: bv16): bool {
    x == y
}

procedure {:inline 1} $int2bv16(src: int) returns (dst: bv16)
{
    if (src > 65535) {
        call $ExecFailureAbort();
        return;
    }
    dst := $int2bv.16(src);
}

procedure {:inline 1} $bv2int16(src: bv16) returns (dst: int)
{
    dst := $bv2int.16(src);
}

function {:builtin "(_ int2bv 16)"} $int2bv.16(i: int) returns (bv16);
function {:builtin "bv2nat"} $bv2int.16(i: bv16) returns (int);

function {:bvbuiltin "bvand"} $And'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvor"} $Or'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvxor"} $Xor'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvadd"} $Add'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvsub"} $Sub'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvmul"} $Mul'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvudiv"} $Div'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvurem"} $Mod'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvshl"} $Shl'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvlshr"} $Shr'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvult"} $Lt'Bv32'(bv32,bv32) returns(bool);
function {:bvbuiltin "bvule"} $Le'Bv32'(bv32,bv32) returns(bool);
function {:bvbuiltin "bvugt"} $Gt'Bv32'(bv32,bv32) returns(bool);
function {:bvbuiltin "bvuge"} $Ge'Bv32'(bv32,bv32) returns(bool);

procedure {:inline 1} $AddBv32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    if ($Lt'Bv32'($Add'Bv32'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Add'Bv32'(src1, src2);
}

procedure {:inline 1} $AddBv32_unchecked(src1: bv32, src2: bv32) returns (dst: bv32)
{
    dst := $Add'Bv32'(src1, src2);
}

procedure {:inline 1} $SubBv32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    if ($Lt'Bv32'(src1, src2)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Sub'Bv32'(src1, src2);
}

procedure {:inline 1} $MulBv32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    if ($Lt'Bv32'($Mul'Bv32'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mul'Bv32'(src1, src2);
}

procedure {:inline 1} $DivBv32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    if (src2 == 0bv32) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Div'Bv32'(src1, src2);
}

procedure {:inline 1} $ModBv32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    if (src2 == 0bv32) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mod'Bv32'(src1, src2);
}

procedure {:inline 1} $AndBv32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    dst := $And'Bv32'(src1,src2);
}

procedure {:inline 1} $OrBv32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    dst := $Or'Bv32'(src1,src2);
}

procedure {:inline 1} $XorBv32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    dst := $Xor'Bv32'(src1,src2);
}

procedure {:inline 1} $LtBv32(src1: bv32, src2: bv32) returns (dst: bool)
{
    dst := $Lt'Bv32'(src1,src2);
}

procedure {:inline 1} $LeBv32(src1: bv32, src2: bv32) returns (dst: bool)
{
    dst := $Le'Bv32'(src1,src2);
}

procedure {:inline 1} $GtBv32(src1: bv32, src2: bv32) returns (dst: bool)
{
    dst := $Gt'Bv32'(src1,src2);
}

procedure {:inline 1} $GeBv32(src1: bv32, src2: bv32) returns (dst: bool)
{
    dst := $Ge'Bv32'(src1,src2);
}

function $IsValid'bv32'(v: bv32): bool {
  $Ge'Bv32'(v,0bv32) && $Le'Bv32'(v,2147483647bv32)
}

function {:inline} $IsEqual'bv32'(x: bv32, y: bv32): bool {
    x == y
}

procedure {:inline 1} $int2bv32(src: int) returns (dst: bv32)
{
    if (src > 2147483647) {
        call $ExecFailureAbort();
        return;
    }
    dst := $int2bv.32(src);
}

procedure {:inline 1} $bv2int32(src: bv32) returns (dst: int)
{
    dst := $bv2int.32(src);
}

function {:builtin "(_ int2bv 32)"} $int2bv.32(i: int) returns (bv32);
function {:builtin "bv2nat"} $bv2int.32(i: bv32) returns (int);

function {:bvbuiltin "bvand"} $And'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvor"} $Or'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvxor"} $Xor'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvadd"} $Add'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvsub"} $Sub'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvmul"} $Mul'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvudiv"} $Div'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvurem"} $Mod'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvshl"} $Shl'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvlshr"} $Shr'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvult"} $Lt'Bv64'(bv64,bv64) returns(bool);
function {:bvbuiltin "bvule"} $Le'Bv64'(bv64,bv64) returns(bool);
function {:bvbuiltin "bvugt"} $Gt'Bv64'(bv64,bv64) returns(bool);
function {:bvbuiltin "bvuge"} $Ge'Bv64'(bv64,bv64) returns(bool);

procedure {:inline 1} $AddBv64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    if ($Lt'Bv64'($Add'Bv64'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Add'Bv64'(src1, src2);
}

procedure {:inline 1} $AddBv64_unchecked(src1: bv64, src2: bv64) returns (dst: bv64)
{
    dst := $Add'Bv64'(src1, src2);
}

procedure {:inline 1} $SubBv64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    if ($Lt'Bv64'(src1, src2)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Sub'Bv64'(src1, src2);
}

procedure {:inline 1} $MulBv64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    if ($Lt'Bv64'($Mul'Bv64'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mul'Bv64'(src1, src2);
}

procedure {:inline 1} $DivBv64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    if (src2 == 0bv64) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Div'Bv64'(src1, src2);
}

procedure {:inline 1} $ModBv64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    if (src2 == 0bv64) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mod'Bv64'(src1, src2);
}

procedure {:inline 1} $AndBv64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    dst := $And'Bv64'(src1,src2);
}

procedure {:inline 1} $OrBv64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    dst := $Or'Bv64'(src1,src2);
}

procedure {:inline 1} $XorBv64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    dst := $Xor'Bv64'(src1,src2);
}

procedure {:inline 1} $LtBv64(src1: bv64, src2: bv64) returns (dst: bool)
{
    dst := $Lt'Bv64'(src1,src2);
}

procedure {:inline 1} $LeBv64(src1: bv64, src2: bv64) returns (dst: bool)
{
    dst := $Le'Bv64'(src1,src2);
}

procedure {:inline 1} $GtBv64(src1: bv64, src2: bv64) returns (dst: bool)
{
    dst := $Gt'Bv64'(src1,src2);
}

procedure {:inline 1} $GeBv64(src1: bv64, src2: bv64) returns (dst: bool)
{
    dst := $Ge'Bv64'(src1,src2);
}

function $IsValid'bv64'(v: bv64): bool {
  $Ge'Bv64'(v,0bv64) && $Le'Bv64'(v,18446744073709551615bv64)
}

function {:inline} $IsEqual'bv64'(x: bv64, y: bv64): bool {
    x == y
}

procedure {:inline 1} $int2bv64(src: int) returns (dst: bv64)
{
    if (src > 18446744073709551615) {
        call $ExecFailureAbort();
        return;
    }
    dst := $int2bv.64(src);
}

procedure {:inline 1} $bv2int64(src: bv64) returns (dst: int)
{
    dst := $bv2int.64(src);
}

function {:builtin "(_ int2bv 64)"} $int2bv.64(i: int) returns (bv64);
function {:builtin "bv2nat"} $bv2int.64(i: bv64) returns (int);

function {:bvbuiltin "bvand"} $And'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvor"} $Or'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvxor"} $Xor'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvadd"} $Add'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvsub"} $Sub'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvmul"} $Mul'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvudiv"} $Div'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvurem"} $Mod'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvshl"} $Shl'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvlshr"} $Shr'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvult"} $Lt'Bv128'(bv128,bv128) returns(bool);
function {:bvbuiltin "bvule"} $Le'Bv128'(bv128,bv128) returns(bool);
function {:bvbuiltin "bvugt"} $Gt'Bv128'(bv128,bv128) returns(bool);
function {:bvbuiltin "bvuge"} $Ge'Bv128'(bv128,bv128) returns(bool);

procedure {:inline 1} $AddBv128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    if ($Lt'Bv128'($Add'Bv128'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Add'Bv128'(src1, src2);
}

procedure {:inline 1} $AddBv128_unchecked(src1: bv128, src2: bv128) returns (dst: bv128)
{
    dst := $Add'Bv128'(src1, src2);
}

procedure {:inline 1} $SubBv128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    if ($Lt'Bv128'(src1, src2)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Sub'Bv128'(src1, src2);
}

procedure {:inline 1} $MulBv128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    if ($Lt'Bv128'($Mul'Bv128'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mul'Bv128'(src1, src2);
}

procedure {:inline 1} $DivBv128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    if (src2 == 0bv128) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Div'Bv128'(src1, src2);
}

procedure {:inline 1} $ModBv128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    if (src2 == 0bv128) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mod'Bv128'(src1, src2);
}

procedure {:inline 1} $AndBv128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    dst := $And'Bv128'(src1,src2);
}

procedure {:inline 1} $OrBv128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    dst := $Or'Bv128'(src1,src2);
}

procedure {:inline 1} $XorBv128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    dst := $Xor'Bv128'(src1,src2);
}

procedure {:inline 1} $LtBv128(src1: bv128, src2: bv128) returns (dst: bool)
{
    dst := $Lt'Bv128'(src1,src2);
}

procedure {:inline 1} $LeBv128(src1: bv128, src2: bv128) returns (dst: bool)
{
    dst := $Le'Bv128'(src1,src2);
}

procedure {:inline 1} $GtBv128(src1: bv128, src2: bv128) returns (dst: bool)
{
    dst := $Gt'Bv128'(src1,src2);
}

procedure {:inline 1} $GeBv128(src1: bv128, src2: bv128) returns (dst: bool)
{
    dst := $Ge'Bv128'(src1,src2);
}

function $IsValid'bv128'(v: bv128): bool {
  $Ge'Bv128'(v,0bv128) && $Le'Bv128'(v,340282366920938463463374607431768211455bv128)
}

function {:inline} $IsEqual'bv128'(x: bv128, y: bv128): bool {
    x == y
}

procedure {:inline 1} $int2bv128(src: int) returns (dst: bv128)
{
    if (src > 340282366920938463463374607431768211455) {
        call $ExecFailureAbort();
        return;
    }
    dst := $int2bv.128(src);
}

procedure {:inline 1} $bv2int128(src: bv128) returns (dst: int)
{
    dst := $bv2int.128(src);
}

function {:builtin "(_ int2bv 128)"} $int2bv.128(i: int) returns (bv128);
function {:builtin "bv2nat"} $bv2int.128(i: bv128) returns (int);

function {:bvbuiltin "bvand"} $And'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvor"} $Or'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvxor"} $Xor'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvadd"} $Add'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvsub"} $Sub'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvmul"} $Mul'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvudiv"} $Div'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvurem"} $Mod'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvshl"} $Shl'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvlshr"} $Shr'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvult"} $Lt'Bv256'(bv256,bv256) returns(bool);
function {:bvbuiltin "bvule"} $Le'Bv256'(bv256,bv256) returns(bool);
function {:bvbuiltin "bvugt"} $Gt'Bv256'(bv256,bv256) returns(bool);
function {:bvbuiltin "bvuge"} $Ge'Bv256'(bv256,bv256) returns(bool);

procedure {:inline 1} $AddBv256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    if ($Lt'Bv256'($Add'Bv256'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Add'Bv256'(src1, src2);
}

procedure {:inline 1} $AddBv256_unchecked(src1: bv256, src2: bv256) returns (dst: bv256)
{
    dst := $Add'Bv256'(src1, src2);
}

procedure {:inline 1} $SubBv256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    if ($Lt'Bv256'(src1, src2)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Sub'Bv256'(src1, src2);
}

procedure {:inline 1} $MulBv256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    if ($Lt'Bv256'($Mul'Bv256'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mul'Bv256'(src1, src2);
}

procedure {:inline 1} $DivBv256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    if (src2 == 0bv256) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Div'Bv256'(src1, src2);
}

procedure {:inline 1} $ModBv256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    if (src2 == 0bv256) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mod'Bv256'(src1, src2);
}

procedure {:inline 1} $AndBv256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    dst := $And'Bv256'(src1,src2);
}

procedure {:inline 1} $OrBv256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    dst := $Or'Bv256'(src1,src2);
}

procedure {:inline 1} $XorBv256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    dst := $Xor'Bv256'(src1,src2);
}

procedure {:inline 1} $LtBv256(src1: bv256, src2: bv256) returns (dst: bool)
{
    dst := $Lt'Bv256'(src1,src2);
}

procedure {:inline 1} $LeBv256(src1: bv256, src2: bv256) returns (dst: bool)
{
    dst := $Le'Bv256'(src1,src2);
}

procedure {:inline 1} $GtBv256(src1: bv256, src2: bv256) returns (dst: bool)
{
    dst := $Gt'Bv256'(src1,src2);
}

procedure {:inline 1} $GeBv256(src1: bv256, src2: bv256) returns (dst: bool)
{
    dst := $Ge'Bv256'(src1,src2);
}

function $IsValid'bv256'(v: bv256): bool {
  $Ge'Bv256'(v,0bv256) && $Le'Bv256'(v,115792089237316195423570985008687907853269984665640564039457584007913129639935bv256)
}

function {:inline} $IsEqual'bv256'(x: bv256, y: bv256): bool {
    x == y
}

procedure {:inline 1} $int2bv256(src: int) returns (dst: bv256)
{
    if (src > 115792089237316195423570985008687907853269984665640564039457584007913129639935) {
        call $ExecFailureAbort();
        return;
    }
    dst := $int2bv.256(src);
}

procedure {:inline 1} $bv2int256(src: bv256) returns (dst: int)
{
    dst := $bv2int.256(src);
}

function {:builtin "(_ int2bv 256)"} $int2bv.256(i: int) returns (bv256);
function {:builtin "bv2nat"} $bv2int.256(i: bv256) returns (int);

datatype $Range {
    $Range(lb: int, ub: int)
}

function {:inline} $IsValid'bool'(v: bool): bool {
  true
}

function $IsValid'u8'(v: int): bool {
  v >= 0 && v <= $MAX_U8
}

function $IsValid'u16'(v: int): bool {
  v >= 0 && v <= $MAX_U16
}

function $IsValid'u32'(v: int): bool {
  v >= 0 && v <= $MAX_U32
}

function $IsValid'u64'(v: int): bool {
  v >= 0 && v <= $MAX_U64
}

function $IsValid'u128'(v: int): bool {
  v >= 0 && v <= $MAX_U128
}

function $IsValid'u256'(v: int): bool {
  v >= 0 && v <= $MAX_U256
}

function $IsValid'num'(v: int): bool {
  true
}

function $IsValid'address'(v: int): bool {
  // TODO: restrict max to representable addresses?
  v >= 0
}

function {:inline} $IsValidRange(r: $Range): bool {
   $IsValid'u64'(r->lb) &&  $IsValid'u64'(r->ub)
}

// Intentionally not inlined so it serves as a trigger in quantifiers.
function $InRange(r: $Range, i: int): bool {
   r->lb <= i && i < r->ub
}


function {:inline} $IsEqual'u8'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'u16'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'u32'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'u64'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'u128'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'u256'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'num'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'address'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'bool'(x: bool, y: bool): bool {
    x == y
}

// ============================================================================================
// Memory

datatype $Location {
    // A global resource location within the statically known resource type's memory,
    // where `a` is an address.
    $Global(a: int),
    // A local location. `i` is the unique index of the local.
    $Local(i: int),
    // The location of a reference outside of the verification scope, for example, a `&mut` parameter
    // of the function being verified. References with these locations don't need to be written back
    // when mutation ends.
    $Param(i: int),
    // The location of an uninitialized mutation. Using this to make sure that the location
    // will not be equal to any valid mutation locations, i.e., $Local, $Global, or $Param.
    $Uninitialized()
}

// A mutable reference which also carries its current value. Since mutable references
// are single threaded in Move, we can keep them together and treat them as a value
// during mutation until the point they are stored back to their original location.
datatype $Mutation<T> {
    $Mutation(l: $Location, p: Vec int, v: T)
}

// Representation of memory for a given type.
datatype $Memory<T> {
    $Memory(domain: [int]bool, contents: [int]T)
}

function {:builtin "MapConst"} $ConstMemoryDomain(v: bool): [int]bool;
function {:builtin "MapConst"} $ConstMemoryContent<T>(v: T): [int]T;
axiom $ConstMemoryDomain(false) == (lambda i: int :: false);
axiom $ConstMemoryDomain(true) == (lambda i: int :: true);


// Dereferences a mutation.
function {:inline} $Dereference<T>(ref: $Mutation T): T {
    ref->v
}

// Update the value of a mutation.
function {:inline} $UpdateMutation<T>(m: $Mutation T, v: T): $Mutation T {
    $Mutation(m->l, m->p, v)
}

function {:inline} $ChildMutation<T1, T2>(m: $Mutation T1, offset: int, v: T2): $Mutation T2 {
    $Mutation(m->l, ExtendVec(m->p, offset), v)
}

// Return true if two mutations share the location and path
function {:inline} $IsSameMutation<T1, T2>(parent: $Mutation T1, child: $Mutation T2 ): bool {
    parent->l == child->l && parent->p == child->p
}

// Return true if the mutation is a parent of a child which was derived with the given edge offset. This
// is used to implement write-back choices.
function {:inline} $IsParentMutation<T1, T2>(parent: $Mutation T1, edge: int, child: $Mutation T2 ): bool {
    parent->l == child->l &&
    (var pp := parent->p;
    (var cp := child->p;
    (var pl := LenVec(pp);
    (var cl := LenVec(cp);
     cl == pl + 1 &&
     (forall i: int:: i >= 0 && i < pl ==> ReadVec(pp, i) ==  ReadVec(cp, i)) &&
     $EdgeMatches(ReadVec(cp, pl), edge)
    ))))
}

// Return true if the mutation is a parent of a child, for hyper edge.
function {:inline} $IsParentMutationHyper<T1, T2>(parent: $Mutation T1, hyper_edge: Vec int, child: $Mutation T2 ): bool {
    parent->l == child->l &&
    (var pp := parent->p;
    (var cp := child->p;
    (var pl := LenVec(pp);
    (var cl := LenVec(cp);
    (var el := LenVec(hyper_edge);
     cl == pl + el &&
     (forall i: int:: i >= 0 && i < pl ==> ReadVec(pp, i) == ReadVec(cp, i)) &&
     (forall i: int:: i >= 0 && i < el ==> $EdgeMatches(ReadVec(cp, pl + i), ReadVec(hyper_edge, i)))
    )))))
}

function {:inline} $EdgeMatches(edge: int, edge_pattern: int): bool {
    edge_pattern == -1 // wildcard
    || edge_pattern == edge
}



function {:inline} $SameLocation<T1, T2>(m1: $Mutation T1, m2: $Mutation T2): bool {
    m1->l == m2->l
}

function {:inline} $HasGlobalLocation<T>(m: $Mutation T): bool {
    (m->l) is $Global
}

function {:inline} $HasLocalLocation<T>(m: $Mutation T, idx: int): bool {
    m->l == $Local(idx)
}

function {:inline} $GlobalLocationAddress<T>(m: $Mutation T): int {
    (m->l)->a
}



// Tests whether resource exists.
function {:inline} $ResourceExists<T>(m: $Memory T, addr: int): bool {
    m->domain[addr]
}

// Obtains Value of given resource.
function {:inline} $ResourceValue<T>(m: $Memory T, addr: int): T {
    m->contents[addr]
}

// Update resource.
function {:inline} $ResourceUpdate<T>(m: $Memory T, a: int, v: T): $Memory T {
    $Memory(m->domain[a := true], m->contents[a := v])
}

// Remove resource.
function {:inline} $ResourceRemove<T>(m: $Memory T, a: int): $Memory T {
    $Memory(m->domain[a := false], m->contents)
}

// Copies resource from memory s to m.
function {:inline} $ResourceCopy<T>(m: $Memory T, s: $Memory T, a: int): $Memory T {
    $Memory(m->domain[a := s->domain[a]],
            m->contents[a := s->contents[a]])
}



// ============================================================================================
// Abort Handling

var $abort_flag: bool;
var $abort_code: int;

function {:inline} $process_abort_code(code: int): int {
    code
}

const $EXEC_FAILURE_CODE: int;
axiom $EXEC_FAILURE_CODE == -1;

// TODO(wrwg): currently we map aborts of native functions like those for vectors also to
//   execution failure. This may need to be aligned with what the runtime actually does.

procedure {:inline 1} $ExecFailureAbort() {
    $abort_flag := true;
    $abort_code := $EXEC_FAILURE_CODE;
}

procedure {:inline 1} $Abort(code: int) {
    $abort_flag := true;
    $abort_code := code;
}

function {:inline} $StdError(cat: int, reason: int): int {
    reason * 256 + cat
}

procedure {:inline 1} $InitVerification() {
    // Set abort_flag to false, and havoc abort_code
    $abort_flag := false;
    havoc $abort_code;
    // Initialize event store
    call $InitEventStore();
}

// ============================================================================================
// Instructions


procedure {:inline 1} $CastU8(src: int) returns (dst: int)
{
    if (src > $MAX_U8) {
        call $ExecFailureAbort();
        return;
    }
    dst := src;
}

procedure {:inline 1} $CastU16(src: int) returns (dst: int)
{
    if (src > $MAX_U16) {
        call $ExecFailureAbort();
        return;
    }
    dst := src;
}

procedure {:inline 1} $CastU32(src: int) returns (dst: int)
{
    if (src > $MAX_U32) {
        call $ExecFailureAbort();
        return;
    }
    dst := src;
}

procedure {:inline 1} $CastU64(src: int) returns (dst: int)
{
    if (src > $MAX_U64) {
        call $ExecFailureAbort();
        return;
    }
    dst := src;
}

procedure {:inline 1} $CastU128(src: int) returns (dst: int)
{
    if (src > $MAX_U128) {
        call $ExecFailureAbort();
        return;
    }
    dst := src;
}

procedure {:inline 1} $CastU256(src: int) returns (dst: int)
{
    if (src > $MAX_U256) {
        call $ExecFailureAbort();
        return;
    }
    dst := src;
}

procedure {:inline 1} $AddU8(src1: int, src2: int) returns (dst: int)
{
    if (src1 + src2 > $MAX_U8) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 + src2;
}

procedure {:inline 1} $AddU16(src1: int, src2: int) returns (dst: int)
{
    if (src1 + src2 > $MAX_U16) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 + src2;
}

procedure {:inline 1} $AddU16_unchecked(src1: int, src2: int) returns (dst: int)
{
    dst := src1 + src2;
}

procedure {:inline 1} $AddU32(src1: int, src2: int) returns (dst: int)
{
    if (src1 + src2 > $MAX_U32) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 + src2;
}

procedure {:inline 1} $AddU32_unchecked(src1: int, src2: int) returns (dst: int)
{
    dst := src1 + src2;
}

procedure {:inline 1} $AddU64(src1: int, src2: int) returns (dst: int)
{
    if (src1 + src2 > $MAX_U64) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 + src2;
}

procedure {:inline 1} $AddU64_unchecked(src1: int, src2: int) returns (dst: int)
{
    dst := src1 + src2;
}

procedure {:inline 1} $AddU128(src1: int, src2: int) returns (dst: int)
{
    if (src1 + src2 > $MAX_U128) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 + src2;
}

procedure {:inline 1} $AddU128_unchecked(src1: int, src2: int) returns (dst: int)
{
    dst := src1 + src2;
}

procedure {:inline 1} $AddU256(src1: int, src2: int) returns (dst: int)
{
    if (src1 + src2 > $MAX_U256) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 + src2;
}

procedure {:inline 1} $AddU256_unchecked(src1: int, src2: int) returns (dst: int)
{
    dst := src1 + src2;
}

procedure {:inline 1} $Sub(src1: int, src2: int) returns (dst: int)
{
    if (src1 < src2) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 - src2;
}

// uninterpreted function to return an undefined value.
function $undefined_int(): int;

// Recursive exponentiation function
// Undefined unless e >=0.  $pow(0,0) is also undefined.
function $pow(n: int, e: int): int {
    if n != 0 && e == 0 then 1
    else if e > 0 then n * $pow(n, e - 1)
    else $undefined_int()
}

function $shl(src1: int, p: int): int {
    src1 * $pow(2, p)
}

function $shlU8(src1: int, p: int): int {
    (src1 * $pow(2, p)) mod 256
}

function $shlU16(src1: int, p: int): int {
    (src1 * $pow(2, p)) mod 65536
}

function $shlU32(src1: int, p: int): int {
    (src1 * $pow(2, p)) mod 4294967296
}

function $shlU64(src1: int, p: int): int {
    (src1 * $pow(2, p)) mod 18446744073709551616
}

function $shlU128(src1: int, p: int): int {
    (src1 * $pow(2, p)) mod 340282366920938463463374607431768211456
}

function $shlU256(src1: int, p: int): int {
    (src1 * $pow(2, p)) mod 115792089237316195423570985008687907853269984665640564039457584007913129639936
}

function $shr(src1: int, p: int): int {
    src1 div $pow(2, p)
}

// We need to know the size of the destination in order to drop bits
// that have been shifted left more than that, so we have $ShlU8/16/32/64/128/256
procedure {:inline 1} $ShlU8(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 8) {
        call $ExecFailureAbort();
        return;
    }
    dst := $shlU8(src1, src2);
}

// Template for cast and shift operations of bitvector types

procedure {:inline 1} $CastBv8to8(src: bv8) returns (dst: bv8)
{
    dst := src;
}


function $shlBv8From8(src1: bv8, src2: bv8) returns (bv8)
{
    $Shl'Bv8'(src1, src2)
}

procedure {:inline 1} $ShlBv8From8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    if ($Ge'Bv8'(src2, 8bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv8'(src1, src2);
}

function $shrBv8From8(src1: bv8, src2: bv8) returns (bv8)
{
    $Shr'Bv8'(src1, src2)
}

procedure {:inline 1} $ShrBv8From8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    if ($Ge'Bv8'(src2, 8bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv8'(src1, src2);
}

procedure {:inline 1} $CastBv16to8(src: bv16) returns (dst: bv8)
{
    if ($Gt'Bv16'(src, 255bv16)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[8:0];
}


function $shlBv8From16(src1: bv8, src2: bv16) returns (bv8)
{
    $Shl'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShlBv8From16(src1: bv8, src2: bv16) returns (dst: bv8)
{
    if ($Ge'Bv16'(src2, 8bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv8'(src1, src2[8:0]);
}

function $shrBv8From16(src1: bv8, src2: bv16) returns (bv8)
{
    $Shr'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShrBv8From16(src1: bv8, src2: bv16) returns (dst: bv8)
{
    if ($Ge'Bv16'(src2, 8bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv8'(src1, src2[8:0]);
}

procedure {:inline 1} $CastBv32to8(src: bv32) returns (dst: bv8)
{
    if ($Gt'Bv32'(src, 255bv32)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[8:0];
}


function $shlBv8From32(src1: bv8, src2: bv32) returns (bv8)
{
    $Shl'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShlBv8From32(src1: bv8, src2: bv32) returns (dst: bv8)
{
    if ($Ge'Bv32'(src2, 8bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv8'(src1, src2[8:0]);
}

function $shrBv8From32(src1: bv8, src2: bv32) returns (bv8)
{
    $Shr'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShrBv8From32(src1: bv8, src2: bv32) returns (dst: bv8)
{
    if ($Ge'Bv32'(src2, 8bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv8'(src1, src2[8:0]);
}

procedure {:inline 1} $CastBv64to8(src: bv64) returns (dst: bv8)
{
    if ($Gt'Bv64'(src, 255bv64)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[8:0];
}


function $shlBv8From64(src1: bv8, src2: bv64) returns (bv8)
{
    $Shl'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShlBv8From64(src1: bv8, src2: bv64) returns (dst: bv8)
{
    if ($Ge'Bv64'(src2, 8bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv8'(src1, src2[8:0]);
}

function $shrBv8From64(src1: bv8, src2: bv64) returns (bv8)
{
    $Shr'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShrBv8From64(src1: bv8, src2: bv64) returns (dst: bv8)
{
    if ($Ge'Bv64'(src2, 8bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv8'(src1, src2[8:0]);
}

procedure {:inline 1} $CastBv128to8(src: bv128) returns (dst: bv8)
{
    if ($Gt'Bv128'(src, 255bv128)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[8:0];
}


function $shlBv8From128(src1: bv8, src2: bv128) returns (bv8)
{
    $Shl'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShlBv8From128(src1: bv8, src2: bv128) returns (dst: bv8)
{
    if ($Ge'Bv128'(src2, 8bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv8'(src1, src2[8:0]);
}

function $shrBv8From128(src1: bv8, src2: bv128) returns (bv8)
{
    $Shr'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShrBv8From128(src1: bv8, src2: bv128) returns (dst: bv8)
{
    if ($Ge'Bv128'(src2, 8bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv8'(src1, src2[8:0]);
}

procedure {:inline 1} $CastBv256to8(src: bv256) returns (dst: bv8)
{
    if ($Gt'Bv256'(src, 255bv256)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[8:0];
}


function $shlBv8From256(src1: bv8, src2: bv256) returns (bv8)
{
    $Shl'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShlBv8From256(src1: bv8, src2: bv256) returns (dst: bv8)
{
    if ($Ge'Bv256'(src2, 8bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv8'(src1, src2[8:0]);
}

function $shrBv8From256(src1: bv8, src2: bv256) returns (bv8)
{
    $Shr'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShrBv8From256(src1: bv8, src2: bv256) returns (dst: bv8)
{
    if ($Ge'Bv256'(src2, 8bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv8'(src1, src2[8:0]);
}

procedure {:inline 1} $CastBv8to16(src: bv8) returns (dst: bv16)
{
    dst := 0bv8 ++ src;
}


function $shlBv16From8(src1: bv16, src2: bv8) returns (bv16)
{
    $Shl'Bv16'(src1, 0bv8 ++ src2)
}

procedure {:inline 1} $ShlBv16From8(src1: bv16, src2: bv8) returns (dst: bv16)
{
    if ($Ge'Bv8'(src2, 16bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv16'(src1, 0bv8 ++ src2);
}

function $shrBv16From8(src1: bv16, src2: bv8) returns (bv16)
{
    $Shr'Bv16'(src1, 0bv8 ++ src2)
}

procedure {:inline 1} $ShrBv16From8(src1: bv16, src2: bv8) returns (dst: bv16)
{
    if ($Ge'Bv8'(src2, 16bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv16'(src1, 0bv8 ++ src2);
}

procedure {:inline 1} $CastBv16to16(src: bv16) returns (dst: bv16)
{
    dst := src;
}


function $shlBv16From16(src1: bv16, src2: bv16) returns (bv16)
{
    $Shl'Bv16'(src1, src2)
}

procedure {:inline 1} $ShlBv16From16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    if ($Ge'Bv16'(src2, 16bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv16'(src1, src2);
}

function $shrBv16From16(src1: bv16, src2: bv16) returns (bv16)
{
    $Shr'Bv16'(src1, src2)
}

procedure {:inline 1} $ShrBv16From16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    if ($Ge'Bv16'(src2, 16bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv16'(src1, src2);
}

procedure {:inline 1} $CastBv32to16(src: bv32) returns (dst: bv16)
{
    if ($Gt'Bv32'(src, 65535bv32)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[16:0];
}


function $shlBv16From32(src1: bv16, src2: bv32) returns (bv16)
{
    $Shl'Bv16'(src1, src2[16:0])
}

procedure {:inline 1} $ShlBv16From32(src1: bv16, src2: bv32) returns (dst: bv16)
{
    if ($Ge'Bv32'(src2, 16bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv16'(src1, src2[16:0]);
}

function $shrBv16From32(src1: bv16, src2: bv32) returns (bv16)
{
    $Shr'Bv16'(src1, src2[16:0])
}

procedure {:inline 1} $ShrBv16From32(src1: bv16, src2: bv32) returns (dst: bv16)
{
    if ($Ge'Bv32'(src2, 16bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv16'(src1, src2[16:0]);
}

procedure {:inline 1} $CastBv64to16(src: bv64) returns (dst: bv16)
{
    if ($Gt'Bv64'(src, 65535bv64)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[16:0];
}


function $shlBv16From64(src1: bv16, src2: bv64) returns (bv16)
{
    $Shl'Bv16'(src1, src2[16:0])
}

procedure {:inline 1} $ShlBv16From64(src1: bv16, src2: bv64) returns (dst: bv16)
{
    if ($Ge'Bv64'(src2, 16bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv16'(src1, src2[16:0]);
}

function $shrBv16From64(src1: bv16, src2: bv64) returns (bv16)
{
    $Shr'Bv16'(src1, src2[16:0])
}

procedure {:inline 1} $ShrBv16From64(src1: bv16, src2: bv64) returns (dst: bv16)
{
    if ($Ge'Bv64'(src2, 16bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv16'(src1, src2[16:0]);
}

procedure {:inline 1} $CastBv128to16(src: bv128) returns (dst: bv16)
{
    if ($Gt'Bv128'(src, 65535bv128)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[16:0];
}


function $shlBv16From128(src1: bv16, src2: bv128) returns (bv16)
{
    $Shl'Bv16'(src1, src2[16:0])
}

procedure {:inline 1} $ShlBv16From128(src1: bv16, src2: bv128) returns (dst: bv16)
{
    if ($Ge'Bv128'(src2, 16bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv16'(src1, src2[16:0]);
}

function $shrBv16From128(src1: bv16, src2: bv128) returns (bv16)
{
    $Shr'Bv16'(src1, src2[16:0])
}

procedure {:inline 1} $ShrBv16From128(src1: bv16, src2: bv128) returns (dst: bv16)
{
    if ($Ge'Bv128'(src2, 16bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv16'(src1, src2[16:0]);
}

procedure {:inline 1} $CastBv256to16(src: bv256) returns (dst: bv16)
{
    if ($Gt'Bv256'(src, 65535bv256)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[16:0];
}


function $shlBv16From256(src1: bv16, src2: bv256) returns (bv16)
{
    $Shl'Bv16'(src1, src2[16:0])
}

procedure {:inline 1} $ShlBv16From256(src1: bv16, src2: bv256) returns (dst: bv16)
{
    if ($Ge'Bv256'(src2, 16bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv16'(src1, src2[16:0]);
}

function $shrBv16From256(src1: bv16, src2: bv256) returns (bv16)
{
    $Shr'Bv16'(src1, src2[16:0])
}

procedure {:inline 1} $ShrBv16From256(src1: bv16, src2: bv256) returns (dst: bv16)
{
    if ($Ge'Bv256'(src2, 16bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv16'(src1, src2[16:0]);
}

procedure {:inline 1} $CastBv8to32(src: bv8) returns (dst: bv32)
{
    dst := 0bv24 ++ src;
}


function $shlBv32From8(src1: bv32, src2: bv8) returns (bv32)
{
    $Shl'Bv32'(src1, 0bv24 ++ src2)
}

procedure {:inline 1} $ShlBv32From8(src1: bv32, src2: bv8) returns (dst: bv32)
{
    if ($Ge'Bv8'(src2, 32bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv32'(src1, 0bv24 ++ src2);
}

function $shrBv32From8(src1: bv32, src2: bv8) returns (bv32)
{
    $Shr'Bv32'(src1, 0bv24 ++ src2)
}

procedure {:inline 1} $ShrBv32From8(src1: bv32, src2: bv8) returns (dst: bv32)
{
    if ($Ge'Bv8'(src2, 32bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv32'(src1, 0bv24 ++ src2);
}

procedure {:inline 1} $CastBv16to32(src: bv16) returns (dst: bv32)
{
    dst := 0bv16 ++ src;
}


function $shlBv32From16(src1: bv32, src2: bv16) returns (bv32)
{
    $Shl'Bv32'(src1, 0bv16 ++ src2)
}

procedure {:inline 1} $ShlBv32From16(src1: bv32, src2: bv16) returns (dst: bv32)
{
    if ($Ge'Bv16'(src2, 32bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv32'(src1, 0bv16 ++ src2);
}

function $shrBv32From16(src1: bv32, src2: bv16) returns (bv32)
{
    $Shr'Bv32'(src1, 0bv16 ++ src2)
}

procedure {:inline 1} $ShrBv32From16(src1: bv32, src2: bv16) returns (dst: bv32)
{
    if ($Ge'Bv16'(src2, 32bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv32'(src1, 0bv16 ++ src2);
}

procedure {:inline 1} $CastBv32to32(src: bv32) returns (dst: bv32)
{
    dst := src;
}


function $shlBv32From32(src1: bv32, src2: bv32) returns (bv32)
{
    $Shl'Bv32'(src1, src2)
}

procedure {:inline 1} $ShlBv32From32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    if ($Ge'Bv32'(src2, 32bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv32'(src1, src2);
}

function $shrBv32From32(src1: bv32, src2: bv32) returns (bv32)
{
    $Shr'Bv32'(src1, src2)
}

procedure {:inline 1} $ShrBv32From32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    if ($Ge'Bv32'(src2, 32bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv32'(src1, src2);
}

procedure {:inline 1} $CastBv64to32(src: bv64) returns (dst: bv32)
{
    if ($Gt'Bv64'(src, 2147483647bv64)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[32:0];
}


function $shlBv32From64(src1: bv32, src2: bv64) returns (bv32)
{
    $Shl'Bv32'(src1, src2[32:0])
}

procedure {:inline 1} $ShlBv32From64(src1: bv32, src2: bv64) returns (dst: bv32)
{
    if ($Ge'Bv64'(src2, 32bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv32'(src1, src2[32:0]);
}

function $shrBv32From64(src1: bv32, src2: bv64) returns (bv32)
{
    $Shr'Bv32'(src1, src2[32:0])
}

procedure {:inline 1} $ShrBv32From64(src1: bv32, src2: bv64) returns (dst: bv32)
{
    if ($Ge'Bv64'(src2, 32bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv32'(src1, src2[32:0]);
}

procedure {:inline 1} $CastBv128to32(src: bv128) returns (dst: bv32)
{
    if ($Gt'Bv128'(src, 2147483647bv128)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[32:0];
}


function $shlBv32From128(src1: bv32, src2: bv128) returns (bv32)
{
    $Shl'Bv32'(src1, src2[32:0])
}

procedure {:inline 1} $ShlBv32From128(src1: bv32, src2: bv128) returns (dst: bv32)
{
    if ($Ge'Bv128'(src2, 32bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv32'(src1, src2[32:0]);
}

function $shrBv32From128(src1: bv32, src2: bv128) returns (bv32)
{
    $Shr'Bv32'(src1, src2[32:0])
}

procedure {:inline 1} $ShrBv32From128(src1: bv32, src2: bv128) returns (dst: bv32)
{
    if ($Ge'Bv128'(src2, 32bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv32'(src1, src2[32:0]);
}

procedure {:inline 1} $CastBv256to32(src: bv256) returns (dst: bv32)
{
    if ($Gt'Bv256'(src, 2147483647bv256)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[32:0];
}


function $shlBv32From256(src1: bv32, src2: bv256) returns (bv32)
{
    $Shl'Bv32'(src1, src2[32:0])
}

procedure {:inline 1} $ShlBv32From256(src1: bv32, src2: bv256) returns (dst: bv32)
{
    if ($Ge'Bv256'(src2, 32bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv32'(src1, src2[32:0]);
}

function $shrBv32From256(src1: bv32, src2: bv256) returns (bv32)
{
    $Shr'Bv32'(src1, src2[32:0])
}

procedure {:inline 1} $ShrBv32From256(src1: bv32, src2: bv256) returns (dst: bv32)
{
    if ($Ge'Bv256'(src2, 32bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv32'(src1, src2[32:0]);
}

procedure {:inline 1} $CastBv8to64(src: bv8) returns (dst: bv64)
{
    dst := 0bv56 ++ src;
}


function $shlBv64From8(src1: bv64, src2: bv8) returns (bv64)
{
    $Shl'Bv64'(src1, 0bv56 ++ src2)
}

procedure {:inline 1} $ShlBv64From8(src1: bv64, src2: bv8) returns (dst: bv64)
{
    if ($Ge'Bv8'(src2, 64bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv64'(src1, 0bv56 ++ src2);
}

function $shrBv64From8(src1: bv64, src2: bv8) returns (bv64)
{
    $Shr'Bv64'(src1, 0bv56 ++ src2)
}

procedure {:inline 1} $ShrBv64From8(src1: bv64, src2: bv8) returns (dst: bv64)
{
    if ($Ge'Bv8'(src2, 64bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv64'(src1, 0bv56 ++ src2);
}

procedure {:inline 1} $CastBv16to64(src: bv16) returns (dst: bv64)
{
    dst := 0bv48 ++ src;
}


function $shlBv64From16(src1: bv64, src2: bv16) returns (bv64)
{
    $Shl'Bv64'(src1, 0bv48 ++ src2)
}

procedure {:inline 1} $ShlBv64From16(src1: bv64, src2: bv16) returns (dst: bv64)
{
    if ($Ge'Bv16'(src2, 64bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv64'(src1, 0bv48 ++ src2);
}

function $shrBv64From16(src1: bv64, src2: bv16) returns (bv64)
{
    $Shr'Bv64'(src1, 0bv48 ++ src2)
}

procedure {:inline 1} $ShrBv64From16(src1: bv64, src2: bv16) returns (dst: bv64)
{
    if ($Ge'Bv16'(src2, 64bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv64'(src1, 0bv48 ++ src2);
}

procedure {:inline 1} $CastBv32to64(src: bv32) returns (dst: bv64)
{
    dst := 0bv32 ++ src;
}


function $shlBv64From32(src1: bv64, src2: bv32) returns (bv64)
{
    $Shl'Bv64'(src1, 0bv32 ++ src2)
}

procedure {:inline 1} $ShlBv64From32(src1: bv64, src2: bv32) returns (dst: bv64)
{
    if ($Ge'Bv32'(src2, 64bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv64'(src1, 0bv32 ++ src2);
}

function $shrBv64From32(src1: bv64, src2: bv32) returns (bv64)
{
    $Shr'Bv64'(src1, 0bv32 ++ src2)
}

procedure {:inline 1} $ShrBv64From32(src1: bv64, src2: bv32) returns (dst: bv64)
{
    if ($Ge'Bv32'(src2, 64bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv64'(src1, 0bv32 ++ src2);
}

procedure {:inline 1} $CastBv64to64(src: bv64) returns (dst: bv64)
{
    dst := src;
}


function $shlBv64From64(src1: bv64, src2: bv64) returns (bv64)
{
    $Shl'Bv64'(src1, src2)
}

procedure {:inline 1} $ShlBv64From64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    if ($Ge'Bv64'(src2, 64bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv64'(src1, src2);
}

function $shrBv64From64(src1: bv64, src2: bv64) returns (bv64)
{
    $Shr'Bv64'(src1, src2)
}

procedure {:inline 1} $ShrBv64From64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    if ($Ge'Bv64'(src2, 64bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv64'(src1, src2);
}

procedure {:inline 1} $CastBv128to64(src: bv128) returns (dst: bv64)
{
    if ($Gt'Bv128'(src, 18446744073709551615bv128)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[64:0];
}


function $shlBv64From128(src1: bv64, src2: bv128) returns (bv64)
{
    $Shl'Bv64'(src1, src2[64:0])
}

procedure {:inline 1} $ShlBv64From128(src1: bv64, src2: bv128) returns (dst: bv64)
{
    if ($Ge'Bv128'(src2, 64bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv64'(src1, src2[64:0]);
}

function $shrBv64From128(src1: bv64, src2: bv128) returns (bv64)
{
    $Shr'Bv64'(src1, src2[64:0])
}

procedure {:inline 1} $ShrBv64From128(src1: bv64, src2: bv128) returns (dst: bv64)
{
    if ($Ge'Bv128'(src2, 64bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv64'(src1, src2[64:0]);
}

procedure {:inline 1} $CastBv256to64(src: bv256) returns (dst: bv64)
{
    if ($Gt'Bv256'(src, 18446744073709551615bv256)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[64:0];
}


function $shlBv64From256(src1: bv64, src2: bv256) returns (bv64)
{
    $Shl'Bv64'(src1, src2[64:0])
}

procedure {:inline 1} $ShlBv64From256(src1: bv64, src2: bv256) returns (dst: bv64)
{
    if ($Ge'Bv256'(src2, 64bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv64'(src1, src2[64:0]);
}

function $shrBv64From256(src1: bv64, src2: bv256) returns (bv64)
{
    $Shr'Bv64'(src1, src2[64:0])
}

procedure {:inline 1} $ShrBv64From256(src1: bv64, src2: bv256) returns (dst: bv64)
{
    if ($Ge'Bv256'(src2, 64bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv64'(src1, src2[64:0]);
}

procedure {:inline 1} $CastBv8to128(src: bv8) returns (dst: bv128)
{
    dst := 0bv120 ++ src;
}


function $shlBv128From8(src1: bv128, src2: bv8) returns (bv128)
{
    $Shl'Bv128'(src1, 0bv120 ++ src2)
}

procedure {:inline 1} $ShlBv128From8(src1: bv128, src2: bv8) returns (dst: bv128)
{
    if ($Ge'Bv8'(src2, 128bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv128'(src1, 0bv120 ++ src2);
}

function $shrBv128From8(src1: bv128, src2: bv8) returns (bv128)
{
    $Shr'Bv128'(src1, 0bv120 ++ src2)
}

procedure {:inline 1} $ShrBv128From8(src1: bv128, src2: bv8) returns (dst: bv128)
{
    if ($Ge'Bv8'(src2, 128bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv128'(src1, 0bv120 ++ src2);
}

procedure {:inline 1} $CastBv16to128(src: bv16) returns (dst: bv128)
{
    dst := 0bv112 ++ src;
}


function $shlBv128From16(src1: bv128, src2: bv16) returns (bv128)
{
    $Shl'Bv128'(src1, 0bv112 ++ src2)
}

procedure {:inline 1} $ShlBv128From16(src1: bv128, src2: bv16) returns (dst: bv128)
{
    if ($Ge'Bv16'(src2, 128bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv128'(src1, 0bv112 ++ src2);
}

function $shrBv128From16(src1: bv128, src2: bv16) returns (bv128)
{
    $Shr'Bv128'(src1, 0bv112 ++ src2)
}

procedure {:inline 1} $ShrBv128From16(src1: bv128, src2: bv16) returns (dst: bv128)
{
    if ($Ge'Bv16'(src2, 128bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv128'(src1, 0bv112 ++ src2);
}

procedure {:inline 1} $CastBv32to128(src: bv32) returns (dst: bv128)
{
    dst := 0bv96 ++ src;
}


function $shlBv128From32(src1: bv128, src2: bv32) returns (bv128)
{
    $Shl'Bv128'(src1, 0bv96 ++ src2)
}

procedure {:inline 1} $ShlBv128From32(src1: bv128, src2: bv32) returns (dst: bv128)
{
    if ($Ge'Bv32'(src2, 128bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv128'(src1, 0bv96 ++ src2);
}

function $shrBv128From32(src1: bv128, src2: bv32) returns (bv128)
{
    $Shr'Bv128'(src1, 0bv96 ++ src2)
}

procedure {:inline 1} $ShrBv128From32(src1: bv128, src2: bv32) returns (dst: bv128)
{
    if ($Ge'Bv32'(src2, 128bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv128'(src1, 0bv96 ++ src2);
}

procedure {:inline 1} $CastBv64to128(src: bv64) returns (dst: bv128)
{
    dst := 0bv64 ++ src;
}


function $shlBv128From64(src1: bv128, src2: bv64) returns (bv128)
{
    $Shl'Bv128'(src1, 0bv64 ++ src2)
}

procedure {:inline 1} $ShlBv128From64(src1: bv128, src2: bv64) returns (dst: bv128)
{
    if ($Ge'Bv64'(src2, 128bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv128'(src1, 0bv64 ++ src2);
}

function $shrBv128From64(src1: bv128, src2: bv64) returns (bv128)
{
    $Shr'Bv128'(src1, 0bv64 ++ src2)
}

procedure {:inline 1} $ShrBv128From64(src1: bv128, src2: bv64) returns (dst: bv128)
{
    if ($Ge'Bv64'(src2, 128bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv128'(src1, 0bv64 ++ src2);
}

procedure {:inline 1} $CastBv128to128(src: bv128) returns (dst: bv128)
{
    dst := src;
}


function $shlBv128From128(src1: bv128, src2: bv128) returns (bv128)
{
    $Shl'Bv128'(src1, src2)
}

procedure {:inline 1} $ShlBv128From128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    if ($Ge'Bv128'(src2, 128bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv128'(src1, src2);
}

function $shrBv128From128(src1: bv128, src2: bv128) returns (bv128)
{
    $Shr'Bv128'(src1, src2)
}

procedure {:inline 1} $ShrBv128From128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    if ($Ge'Bv128'(src2, 128bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv128'(src1, src2);
}

procedure {:inline 1} $CastBv256to128(src: bv256) returns (dst: bv128)
{
    if ($Gt'Bv256'(src, 340282366920938463463374607431768211455bv256)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[128:0];
}


function $shlBv128From256(src1: bv128, src2: bv256) returns (bv128)
{
    $Shl'Bv128'(src1, src2[128:0])
}

procedure {:inline 1} $ShlBv128From256(src1: bv128, src2: bv256) returns (dst: bv128)
{
    if ($Ge'Bv256'(src2, 128bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv128'(src1, src2[128:0]);
}

function $shrBv128From256(src1: bv128, src2: bv256) returns (bv128)
{
    $Shr'Bv128'(src1, src2[128:0])
}

procedure {:inline 1} $ShrBv128From256(src1: bv128, src2: bv256) returns (dst: bv128)
{
    if ($Ge'Bv256'(src2, 128bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv128'(src1, src2[128:0]);
}

procedure {:inline 1} $CastBv8to256(src: bv8) returns (dst: bv256)
{
    dst := 0bv248 ++ src;
}


function $shlBv256From8(src1: bv256, src2: bv8) returns (bv256)
{
    $Shl'Bv256'(src1, 0bv248 ++ src2)
}

procedure {:inline 1} $ShlBv256From8(src1: bv256, src2: bv8) returns (dst: bv256)
{
    if ($Ge'Bv8'(src2, 256bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv256'(src1, 0bv248 ++ src2);
}

function $shrBv256From8(src1: bv256, src2: bv8) returns (bv256)
{
    $Shr'Bv256'(src1, 0bv248 ++ src2)
}

procedure {:inline 1} $ShrBv256From8(src1: bv256, src2: bv8) returns (dst: bv256)
{
    if ($Ge'Bv8'(src2, 256bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv256'(src1, 0bv248 ++ src2);
}

procedure {:inline 1} $CastBv16to256(src: bv16) returns (dst: bv256)
{
    dst := 0bv240 ++ src;
}


function $shlBv256From16(src1: bv256, src2: bv16) returns (bv256)
{
    $Shl'Bv256'(src1, 0bv240 ++ src2)
}

procedure {:inline 1} $ShlBv256From16(src1: bv256, src2: bv16) returns (dst: bv256)
{
    if ($Ge'Bv16'(src2, 256bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv256'(src1, 0bv240 ++ src2);
}

function $shrBv256From16(src1: bv256, src2: bv16) returns (bv256)
{
    $Shr'Bv256'(src1, 0bv240 ++ src2)
}

procedure {:inline 1} $ShrBv256From16(src1: bv256, src2: bv16) returns (dst: bv256)
{
    if ($Ge'Bv16'(src2, 256bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv256'(src1, 0bv240 ++ src2);
}

procedure {:inline 1} $CastBv32to256(src: bv32) returns (dst: bv256)
{
    dst := 0bv224 ++ src;
}


function $shlBv256From32(src1: bv256, src2: bv32) returns (bv256)
{
    $Shl'Bv256'(src1, 0bv224 ++ src2)
}

procedure {:inline 1} $ShlBv256From32(src1: bv256, src2: bv32) returns (dst: bv256)
{
    if ($Ge'Bv32'(src2, 256bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv256'(src1, 0bv224 ++ src2);
}

function $shrBv256From32(src1: bv256, src2: bv32) returns (bv256)
{
    $Shr'Bv256'(src1, 0bv224 ++ src2)
}

procedure {:inline 1} $ShrBv256From32(src1: bv256, src2: bv32) returns (dst: bv256)
{
    if ($Ge'Bv32'(src2, 256bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv256'(src1, 0bv224 ++ src2);
}

procedure {:inline 1} $CastBv64to256(src: bv64) returns (dst: bv256)
{
    dst := 0bv192 ++ src;
}


function $shlBv256From64(src1: bv256, src2: bv64) returns (bv256)
{
    $Shl'Bv256'(src1, 0bv192 ++ src2)
}

procedure {:inline 1} $ShlBv256From64(src1: bv256, src2: bv64) returns (dst: bv256)
{
    if ($Ge'Bv64'(src2, 256bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv256'(src1, 0bv192 ++ src2);
}

function $shrBv256From64(src1: bv256, src2: bv64) returns (bv256)
{
    $Shr'Bv256'(src1, 0bv192 ++ src2)
}

procedure {:inline 1} $ShrBv256From64(src1: bv256, src2: bv64) returns (dst: bv256)
{
    if ($Ge'Bv64'(src2, 256bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv256'(src1, 0bv192 ++ src2);
}

procedure {:inline 1} $CastBv128to256(src: bv128) returns (dst: bv256)
{
    dst := 0bv128 ++ src;
}


function $shlBv256From128(src1: bv256, src2: bv128) returns (bv256)
{
    $Shl'Bv256'(src1, 0bv128 ++ src2)
}

procedure {:inline 1} $ShlBv256From128(src1: bv256, src2: bv128) returns (dst: bv256)
{
    if ($Ge'Bv128'(src2, 256bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv256'(src1, 0bv128 ++ src2);
}

function $shrBv256From128(src1: bv256, src2: bv128) returns (bv256)
{
    $Shr'Bv256'(src1, 0bv128 ++ src2)
}

procedure {:inline 1} $ShrBv256From128(src1: bv256, src2: bv128) returns (dst: bv256)
{
    if ($Ge'Bv128'(src2, 256bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv256'(src1, 0bv128 ++ src2);
}

procedure {:inline 1} $CastBv256to256(src: bv256) returns (dst: bv256)
{
    dst := src;
}


function $shlBv256From256(src1: bv256, src2: bv256) returns (bv256)
{
    $Shl'Bv256'(src1, src2)
}

procedure {:inline 1} $ShlBv256From256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    if ($Ge'Bv256'(src2, 256bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv256'(src1, src2);
}

function $shrBv256From256(src1: bv256, src2: bv256) returns (bv256)
{
    $Shr'Bv256'(src1, src2)
}

procedure {:inline 1} $ShrBv256From256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    if ($Ge'Bv256'(src2, 256bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv256'(src1, src2);
}

procedure {:inline 1} $ShlU16(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 16) {
        call $ExecFailureAbort();
        return;
    }
    dst := $shlU16(src1, src2);
}

procedure {:inline 1} $ShlU32(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 32) {
        call $ExecFailureAbort();
        return;
    }
    dst := $shlU32(src1, src2);
}

procedure {:inline 1} $ShlU64(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 64) {
       call $ExecFailureAbort();
       return;
    }
    dst := $shlU64(src1, src2);
}

procedure {:inline 1} $ShlU128(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 128) {
        call $ExecFailureAbort();
        return;
    }
    dst := $shlU128(src1, src2);
}

procedure {:inline 1} $ShlU256(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    dst := $shlU256(src1, src2);
}

procedure {:inline 1} $Shr(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    dst := $shr(src1, src2);
}

procedure {:inline 1} $ShrU8(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 8) {
        call $ExecFailureAbort();
        return;
    }
    dst := $shr(src1, src2);
}

procedure {:inline 1} $ShrU16(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 16) {
        call $ExecFailureAbort();
        return;
    }
    dst := $shr(src1, src2);
}

procedure {:inline 1} $ShrU32(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 32) {
        call $ExecFailureAbort();
        return;
    }
    dst := $shr(src1, src2);
}

procedure {:inline 1} $ShrU64(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 64) {
        call $ExecFailureAbort();
        return;
    }
    dst := $shr(src1, src2);
}

procedure {:inline 1} $ShrU128(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 128) {
        call $ExecFailureAbort();
        return;
    }
    dst := $shr(src1, src2);
}

procedure {:inline 1} $ShrU256(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    dst := $shr(src1, src2);
}

procedure {:inline 1} $MulU8(src1: int, src2: int) returns (dst: int)
{
    if (src1 * src2 > $MAX_U8) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 * src2;
}

procedure {:inline 1} $MulU16(src1: int, src2: int) returns (dst: int)
{
    if (src1 * src2 > $MAX_U16) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 * src2;
}

procedure {:inline 1} $MulU32(src1: int, src2: int) returns (dst: int)
{
    if (src1 * src2 > $MAX_U32) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 * src2;
}

procedure {:inline 1} $MulU64(src1: int, src2: int) returns (dst: int)
{
    if (src1 * src2 > $MAX_U64) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 * src2;
}

procedure {:inline 1} $MulU128(src1: int, src2: int) returns (dst: int)
{
    if (src1 * src2 > $MAX_U128) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 * src2;
}

procedure {:inline 1} $MulU256(src1: int, src2: int) returns (dst: int)
{
    if (src1 * src2 > $MAX_U256) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 * src2;
}

procedure {:inline 1} $Div(src1: int, src2: int) returns (dst: int)
{
    if (src2 == 0) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 div src2;
}

procedure {:inline 1} $Mod(src1: int, src2: int) returns (dst: int)
{
    if (src2 == 0) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 mod src2;
}

procedure {:inline 1} $ArithBinaryUnimplemented(src1: int, src2: int) returns (dst: int);

procedure {:inline 1} $Lt(src1: int, src2: int) returns (dst: bool)
{
    dst := src1 < src2;
}

procedure {:inline 1} $Gt(src1: int, src2: int) returns (dst: bool)
{
    dst := src1 > src2;
}

procedure {:inline 1} $Le(src1: int, src2: int) returns (dst: bool)
{
    dst := src1 <= src2;
}

procedure {:inline 1} $Ge(src1: int, src2: int) returns (dst: bool)
{
    dst := src1 >= src2;
}

procedure {:inline 1} $And(src1: bool, src2: bool) returns (dst: bool)
{
    dst := src1 && src2;
}

procedure {:inline 1} $Or(src1: bool, src2: bool) returns (dst: bool)
{
    dst := src1 || src2;
}

procedure {:inline 1} $Not(src: bool) returns (dst: bool)
{
    dst := !src;
}

// Pack and Unpack are auto-generated for each type T


// ==================================================================================
// Native Vector

function {:inline} $SliceVecByRange<T>(v: Vec T, r: $Range): Vec T {
    SliceVec(v, r->lb, r->ub)
}

// ----------------------------------------------------------------------------------
// Native Vector implementation for element type `#0`

// Not inlined. It appears faster this way.
function $IsEqual'vec'#0''(v1: Vec (#0), v2: Vec (#0)): bool {
    LenVec(v1) == LenVec(v2) &&
    (forall i: int:: InRangeVec(v1, i) ==> $IsEqual'#0'(ReadVec(v1, i), ReadVec(v2, i)))
}

// Not inlined.
function $IsPrefix'vec'#0''(v: Vec (#0), prefix: Vec (#0)): bool {
    LenVec(v) >= LenVec(prefix) &&
    (forall i: int:: InRangeVec(prefix, i) ==> $IsEqual'#0'(ReadVec(v, i), ReadVec(prefix, i)))
}

// Not inlined.
function $IsSuffix'vec'#0''(v: Vec (#0), suffix: Vec (#0)): bool {
    LenVec(v) >= LenVec(suffix) &&
    (forall i: int:: InRangeVec(suffix, i) ==> $IsEqual'#0'(ReadVec(v, LenVec(v) - LenVec(suffix) + i), ReadVec(suffix, i)))
}

// Not inlined.
function $IsValid'vec'#0''(v: Vec (#0)): bool {
    $IsValid'u64'(LenVec(v)) &&
    (forall i: int:: InRangeVec(v, i) ==> $IsValid'#0'(ReadVec(v, i)))
}


function {:inline} $ContainsVec'#0'(v: Vec (#0), e: #0): bool {
    (exists i: int :: $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'#0'(ReadVec(v, i), e))
}

function $IndexOfVec'#0'(v: Vec (#0), e: #0): int;
axiom (forall v: Vec (#0), e: #0:: {$IndexOfVec'#0'(v, e)}
    (var i := $IndexOfVec'#0'(v, e);
     if (!$ContainsVec'#0'(v, e)) then i == -1
     else $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'#0'(ReadVec(v, i), e) &&
        (forall j: int :: $IsValid'u64'(j) && j >= 0 && j < i ==> !$IsEqual'#0'(ReadVec(v, j), e))));


function {:inline} $RangeVec'#0'(v: Vec (#0)): $Range {
    $Range(0, LenVec(v))
}


function {:inline} $EmptyVec'#0'(): Vec (#0) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_empty'#0'() returns (v: Vec (#0)) {
    v := EmptyVec();
}

function {:inline} $1_vector_$empty'#0'(): Vec (#0) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_is_empty'#0'(v: Vec (#0)) returns (b: bool) {
    b := IsEmptyVec(v);
}

procedure {:inline 1} $1_vector_push_back'#0'(m: $Mutation (Vec (#0)), val: #0) returns (m': $Mutation (Vec (#0))) {
    m' := $UpdateMutation(m, ExtendVec($Dereference(m), val));
}

function {:inline} $1_vector_$push_back'#0'(v: Vec (#0), val: #0): Vec (#0) {
    ExtendVec(v, val)
}

procedure {:inline 1} $1_vector_pop_back'#0'(m: $Mutation (Vec (#0))) returns (e: #0, m': $Mutation (Vec (#0))) {
    var v: Vec (#0);
    var len: int;
    v := $Dereference(m);
    len := LenVec(v);
    if (len == 0) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, len-1);
    m' := $UpdateMutation(m, RemoveVec(v));
}

procedure {:inline 1} $1_vector_append'#0'(m: $Mutation (Vec (#0)), other: Vec (#0)) returns (m': $Mutation (Vec (#0))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), other));
}

procedure {:inline 1} $1_vector_reverse'#0'(m: $Mutation (Vec (#0))) returns (m': $Mutation (Vec (#0))) {
    m' := $UpdateMutation(m, ReverseVec($Dereference(m)));
}

procedure {:inline 1} $1_vector_reverse_append'#0'(m: $Mutation (Vec (#0)), other: Vec (#0)) returns (m': $Mutation (Vec (#0))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), ReverseVec(other)));
}

procedure {:inline 1} $1_vector_trim_reverse'#0'(m: $Mutation (Vec (#0)), new_len: int) returns (v: (Vec (#0)), m': $Mutation (Vec (#0))) {
    var len: int;
    v := $Dereference(m);
    if (LenVec(v) < new_len) {
        call $ExecFailureAbort();
        return;
    }
    v := SliceVec(v, new_len, LenVec(v));
    v := ReverseVec(v);
    m' := $UpdateMutation(m, SliceVec($Dereference(m), 0, new_len));
}

procedure {:inline 1} $1_vector_trim'#0'(m: $Mutation (Vec (#0)), new_len: int) returns (v: (Vec (#0)), m': $Mutation (Vec (#0))) {
    var len: int;
    v := $Dereference(m);
    if (LenVec(v) < new_len) {
        call $ExecFailureAbort();
        return;
    }
    v := SliceVec(v, new_len, LenVec(v));
    m' := $UpdateMutation(m, SliceVec($Dereference(m), 0, new_len));
}

procedure {:inline 1} $1_vector_reverse_slice'#0'(m: $Mutation (Vec (#0)), left: int, right: int) returns (m': $Mutation (Vec (#0))) {
    var left_vec: Vec (#0);
    var mid_vec: Vec (#0);
    var right_vec: Vec (#0);
    var v: Vec (#0);
    if (left > right) {
        call $ExecFailureAbort();
        return;
    }
    if (left == right) {
        m' := m;
        return;
    }
    v := $Dereference(m);
    if (!(right >= 0 && right <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    left_vec := SliceVec(v, 0, left);
    right_vec := SliceVec(v, right, LenVec(v));
    mid_vec := ReverseVec(SliceVec(v, left, right));
    m' := $UpdateMutation(m, ConcatVec(left_vec, ConcatVec(mid_vec, right_vec)));
}

procedure {:inline 1} $1_vector_rotate'#0'(m: $Mutation (Vec (#0)), rot: int) returns (n: int, m': $Mutation (Vec (#0))) {
    var v: Vec (#0);
    var len: int;
    var left_vec: Vec (#0);
    var right_vec: Vec (#0);
    v := $Dereference(m);
    if (!(rot >= 0 && rot <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    left_vec := SliceVec(v, 0, rot);
    right_vec := SliceVec(v, rot, LenVec(v));
    m' := $UpdateMutation(m, ConcatVec(right_vec, left_vec));
    n := LenVec(v) - rot;
}

procedure {:inline 1} $1_vector_rotate_slice'#0'(m: $Mutation (Vec (#0)), left: int, rot: int, right: int) returns (n: int, m': $Mutation (Vec (#0))) {
    var left_vec: Vec (#0);
    var mid_vec: Vec (#0);
    var right_vec: Vec (#0);
    var mid_left_vec: Vec (#0);
    var mid_right_vec: Vec (#0);
    var v: Vec (#0);
    v := $Dereference(m);
    if (!(left <= rot && rot <= right)) {
        call $ExecFailureAbort();
        return;
    }
    if (!(right >= 0 && right <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    v := $Dereference(m);
    left_vec := SliceVec(v, 0, left);
    right_vec := SliceVec(v, right, LenVec(v));
    mid_left_vec := SliceVec(v, left, rot);
    mid_right_vec := SliceVec(v, rot, right);
    mid_vec := ConcatVec(mid_right_vec, mid_left_vec);
    m' := $UpdateMutation(m, ConcatVec(left_vec, ConcatVec(mid_vec, right_vec)));
    n := left + (right - rot);
}

procedure {:inline 1} $1_vector_insert'#0'(m: $Mutation (Vec (#0)), i: int, e: #0) returns (m': $Mutation (Vec (#0))) {
    var left_vec: Vec (#0);
    var right_vec: Vec (#0);
    var v: Vec (#0);
    v := $Dereference(m);
    if (!(i >= 0 && i <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    if (i == LenVec(v)) {
        m' := $UpdateMutation(m, ExtendVec(v, e));
    } else {
        left_vec := ExtendVec(SliceVec(v, 0, i), e);
        right_vec := SliceVec(v, i, LenVec(v));
        m' := $UpdateMutation(m, ConcatVec(left_vec, right_vec));
    }
}

procedure {:inline 1} $1_vector_length'#0'(v: Vec (#0)) returns (l: int) {
    l := LenVec(v);
}

function {:inline} $1_vector_$length'#0'(v: Vec (#0)): int {
    LenVec(v)
}

procedure {:inline 1} $1_vector_borrow'#0'(v: Vec (#0), i: int) returns (dst: #0) {
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    dst := ReadVec(v, i);
}

function {:inline} $1_vector_$borrow'#0'(v: Vec (#0), i: int): #0 {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_borrow_mut'#0'(m: $Mutation (Vec (#0)), index: int)
returns (dst: $Mutation (#0), m': $Mutation (Vec (#0)))
{
    var v: Vec (#0);
    v := $Dereference(m);
    if (!InRangeVec(v, index)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mutation(m->l, ExtendVec(m->p, index), ReadVec(v, index));
    m' := m;
}

function {:inline} $1_vector_$borrow_mut'#0'(v: Vec (#0), i: int): #0 {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_destroy_empty'#0'(v: Vec (#0)) {
    if (!IsEmptyVec(v)) {
      call $ExecFailureAbort();
    }
}

procedure {:inline 1} $1_vector_swap'#0'(m: $Mutation (Vec (#0)), i: int, j: int) returns (m': $Mutation (Vec (#0)))
{
    var v: Vec (#0);
    v := $Dereference(m);
    if (!InRangeVec(v, i) || !InRangeVec(v, j)) {
        call $ExecFailureAbort();
        return;
    }
    m' := $UpdateMutation(m, SwapVec(v, i, j));
}

function {:inline} $1_vector_$swap'#0'(v: Vec (#0), i: int, j: int): Vec (#0) {
    SwapVec(v, i, j)
}

procedure {:inline 1} $1_vector_remove'#0'(m: $Mutation (Vec (#0)), i: int) returns (e: #0, m': $Mutation (Vec (#0)))
{
    var v: Vec (#0);

    v := $Dereference(m);

    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveAtVec(v, i));
}

procedure {:inline 1} $1_vector_swap_remove'#0'(m: $Mutation (Vec (#0)), i: int) returns (e: #0, m': $Mutation (Vec (#0)))
{
    var len: int;
    var v: Vec (#0);

    v := $Dereference(m);
    len := LenVec(v);
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveVec(SwapVec(v, i, len-1)));
}

procedure {:inline 1} $1_vector_contains'#0'(v: Vec (#0), e: #0) returns (res: bool)  {
    res := $ContainsVec'#0'(v, e);
}

procedure {:inline 1}
$1_vector_index_of'#0'(v: Vec (#0), e: #0) returns (res1: bool, res2: int) {
    res2 := $IndexOfVec'#0'(v, e);
    if (res2 >= 0) {
        res1 := true;
    } else {
        res1 := false;
        res2 := 0;
    }
}


// ----------------------------------------------------------------------------------
// Native Vector implementation for element type `address`

// Not inlined. It appears faster this way.
function $IsEqual'vec'address''(v1: Vec (int), v2: Vec (int)): bool {
    LenVec(v1) == LenVec(v2) &&
    (forall i: int:: InRangeVec(v1, i) ==> $IsEqual'address'(ReadVec(v1, i), ReadVec(v2, i)))
}

// Not inlined.
function $IsPrefix'vec'address''(v: Vec (int), prefix: Vec (int)): bool {
    LenVec(v) >= LenVec(prefix) &&
    (forall i: int:: InRangeVec(prefix, i) ==> $IsEqual'address'(ReadVec(v, i), ReadVec(prefix, i)))
}

// Not inlined.
function $IsSuffix'vec'address''(v: Vec (int), suffix: Vec (int)): bool {
    LenVec(v) >= LenVec(suffix) &&
    (forall i: int:: InRangeVec(suffix, i) ==> $IsEqual'address'(ReadVec(v, LenVec(v) - LenVec(suffix) + i), ReadVec(suffix, i)))
}

// Not inlined.
function $IsValid'vec'address''(v: Vec (int)): bool {
    $IsValid'u64'(LenVec(v)) &&
    (forall i: int:: InRangeVec(v, i) ==> $IsValid'address'(ReadVec(v, i)))
}


function {:inline} $ContainsVec'address'(v: Vec (int), e: int): bool {
    (exists i: int :: $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'address'(ReadVec(v, i), e))
}

function $IndexOfVec'address'(v: Vec (int), e: int): int;
axiom (forall v: Vec (int), e: int:: {$IndexOfVec'address'(v, e)}
    (var i := $IndexOfVec'address'(v, e);
     if (!$ContainsVec'address'(v, e)) then i == -1
     else $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'address'(ReadVec(v, i), e) &&
        (forall j: int :: $IsValid'u64'(j) && j >= 0 && j < i ==> !$IsEqual'address'(ReadVec(v, j), e))));


function {:inline} $RangeVec'address'(v: Vec (int)): $Range {
    $Range(0, LenVec(v))
}


function {:inline} $EmptyVec'address'(): Vec (int) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_empty'address'() returns (v: Vec (int)) {
    v := EmptyVec();
}

function {:inline} $1_vector_$empty'address'(): Vec (int) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_is_empty'address'(v: Vec (int)) returns (b: bool) {
    b := IsEmptyVec(v);
}

procedure {:inline 1} $1_vector_push_back'address'(m: $Mutation (Vec (int)), val: int) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ExtendVec($Dereference(m), val));
}

function {:inline} $1_vector_$push_back'address'(v: Vec (int), val: int): Vec (int) {
    ExtendVec(v, val)
}

procedure {:inline 1} $1_vector_pop_back'address'(m: $Mutation (Vec (int))) returns (e: int, m': $Mutation (Vec (int))) {
    var v: Vec (int);
    var len: int;
    v := $Dereference(m);
    len := LenVec(v);
    if (len == 0) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, len-1);
    m' := $UpdateMutation(m, RemoveVec(v));
}

procedure {:inline 1} $1_vector_append'address'(m: $Mutation (Vec (int)), other: Vec (int)) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), other));
}

procedure {:inline 1} $1_vector_reverse'address'(m: $Mutation (Vec (int))) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ReverseVec($Dereference(m)));
}

procedure {:inline 1} $1_vector_reverse_append'address'(m: $Mutation (Vec (int)), other: Vec (int)) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), ReverseVec(other)));
}

procedure {:inline 1} $1_vector_trim_reverse'address'(m: $Mutation (Vec (int)), new_len: int) returns (v: (Vec (int)), m': $Mutation (Vec (int))) {
    var len: int;
    v := $Dereference(m);
    if (LenVec(v) < new_len) {
        call $ExecFailureAbort();
        return;
    }
    v := SliceVec(v, new_len, LenVec(v));
    v := ReverseVec(v);
    m' := $UpdateMutation(m, SliceVec($Dereference(m), 0, new_len));
}

procedure {:inline 1} $1_vector_trim'address'(m: $Mutation (Vec (int)), new_len: int) returns (v: (Vec (int)), m': $Mutation (Vec (int))) {
    var len: int;
    v := $Dereference(m);
    if (LenVec(v) < new_len) {
        call $ExecFailureAbort();
        return;
    }
    v := SliceVec(v, new_len, LenVec(v));
    m' := $UpdateMutation(m, SliceVec($Dereference(m), 0, new_len));
}

procedure {:inline 1} $1_vector_reverse_slice'address'(m: $Mutation (Vec (int)), left: int, right: int) returns (m': $Mutation (Vec (int))) {
    var left_vec: Vec (int);
    var mid_vec: Vec (int);
    var right_vec: Vec (int);
    var v: Vec (int);
    if (left > right) {
        call $ExecFailureAbort();
        return;
    }
    if (left == right) {
        m' := m;
        return;
    }
    v := $Dereference(m);
    if (!(right >= 0 && right <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    left_vec := SliceVec(v, 0, left);
    right_vec := SliceVec(v, right, LenVec(v));
    mid_vec := ReverseVec(SliceVec(v, left, right));
    m' := $UpdateMutation(m, ConcatVec(left_vec, ConcatVec(mid_vec, right_vec)));
}

procedure {:inline 1} $1_vector_rotate'address'(m: $Mutation (Vec (int)), rot: int) returns (n: int, m': $Mutation (Vec (int))) {
    var v: Vec (int);
    var len: int;
    var left_vec: Vec (int);
    var right_vec: Vec (int);
    v := $Dereference(m);
    if (!(rot >= 0 && rot <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    left_vec := SliceVec(v, 0, rot);
    right_vec := SliceVec(v, rot, LenVec(v));
    m' := $UpdateMutation(m, ConcatVec(right_vec, left_vec));
    n := LenVec(v) - rot;
}

procedure {:inline 1} $1_vector_rotate_slice'address'(m: $Mutation (Vec (int)), left: int, rot: int, right: int) returns (n: int, m': $Mutation (Vec (int))) {
    var left_vec: Vec (int);
    var mid_vec: Vec (int);
    var right_vec: Vec (int);
    var mid_left_vec: Vec (int);
    var mid_right_vec: Vec (int);
    var v: Vec (int);
    v := $Dereference(m);
    if (!(left <= rot && rot <= right)) {
        call $ExecFailureAbort();
        return;
    }
    if (!(right >= 0 && right <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    v := $Dereference(m);
    left_vec := SliceVec(v, 0, left);
    right_vec := SliceVec(v, right, LenVec(v));
    mid_left_vec := SliceVec(v, left, rot);
    mid_right_vec := SliceVec(v, rot, right);
    mid_vec := ConcatVec(mid_right_vec, mid_left_vec);
    m' := $UpdateMutation(m, ConcatVec(left_vec, ConcatVec(mid_vec, right_vec)));
    n := left + (right - rot);
}

procedure {:inline 1} $1_vector_insert'address'(m: $Mutation (Vec (int)), i: int, e: int) returns (m': $Mutation (Vec (int))) {
    var left_vec: Vec (int);
    var right_vec: Vec (int);
    var v: Vec (int);
    v := $Dereference(m);
    if (!(i >= 0 && i <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    if (i == LenVec(v)) {
        m' := $UpdateMutation(m, ExtendVec(v, e));
    } else {
        left_vec := ExtendVec(SliceVec(v, 0, i), e);
        right_vec := SliceVec(v, i, LenVec(v));
        m' := $UpdateMutation(m, ConcatVec(left_vec, right_vec));
    }
}

procedure {:inline 1} $1_vector_length'address'(v: Vec (int)) returns (l: int) {
    l := LenVec(v);
}

function {:inline} $1_vector_$length'address'(v: Vec (int)): int {
    LenVec(v)
}

procedure {:inline 1} $1_vector_borrow'address'(v: Vec (int), i: int) returns (dst: int) {
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    dst := ReadVec(v, i);
}

function {:inline} $1_vector_$borrow'address'(v: Vec (int), i: int): int {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_borrow_mut'address'(m: $Mutation (Vec (int)), index: int)
returns (dst: $Mutation (int), m': $Mutation (Vec (int)))
{
    var v: Vec (int);
    v := $Dereference(m);
    if (!InRangeVec(v, index)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mutation(m->l, ExtendVec(m->p, index), ReadVec(v, index));
    m' := m;
}

function {:inline} $1_vector_$borrow_mut'address'(v: Vec (int), i: int): int {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_destroy_empty'address'(v: Vec (int)) {
    if (!IsEmptyVec(v)) {
      call $ExecFailureAbort();
    }
}

procedure {:inline 1} $1_vector_swap'address'(m: $Mutation (Vec (int)), i: int, j: int) returns (m': $Mutation (Vec (int)))
{
    var v: Vec (int);
    v := $Dereference(m);
    if (!InRangeVec(v, i) || !InRangeVec(v, j)) {
        call $ExecFailureAbort();
        return;
    }
    m' := $UpdateMutation(m, SwapVec(v, i, j));
}

function {:inline} $1_vector_$swap'address'(v: Vec (int), i: int, j: int): Vec (int) {
    SwapVec(v, i, j)
}

procedure {:inline 1} $1_vector_remove'address'(m: $Mutation (Vec (int)), i: int) returns (e: int, m': $Mutation (Vec (int)))
{
    var v: Vec (int);

    v := $Dereference(m);

    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveAtVec(v, i));
}

procedure {:inline 1} $1_vector_swap_remove'address'(m: $Mutation (Vec (int)), i: int) returns (e: int, m': $Mutation (Vec (int)))
{
    var len: int;
    var v: Vec (int);

    v := $Dereference(m);
    len := LenVec(v);
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveVec(SwapVec(v, i, len-1)));
}

procedure {:inline 1} $1_vector_contains'address'(v: Vec (int), e: int) returns (res: bool)  {
    res := $ContainsVec'address'(v, e);
}

procedure {:inline 1}
$1_vector_index_of'address'(v: Vec (int), e: int) returns (res1: bool, res2: int) {
    res2 := $IndexOfVec'address'(v, e);
    if (res2 >= 0) {
        res1 := true;
    } else {
        res1 := false;
        res2 := 0;
    }
}


// ----------------------------------------------------------------------------------
// Native Vector implementation for element type `u8`

// Not inlined. It appears faster this way.
function $IsEqual'vec'u8''(v1: Vec (int), v2: Vec (int)): bool {
    LenVec(v1) == LenVec(v2) &&
    (forall i: int:: InRangeVec(v1, i) ==> $IsEqual'u8'(ReadVec(v1, i), ReadVec(v2, i)))
}

// Not inlined.
function $IsPrefix'vec'u8''(v: Vec (int), prefix: Vec (int)): bool {
    LenVec(v) >= LenVec(prefix) &&
    (forall i: int:: InRangeVec(prefix, i) ==> $IsEqual'u8'(ReadVec(v, i), ReadVec(prefix, i)))
}

// Not inlined.
function $IsSuffix'vec'u8''(v: Vec (int), suffix: Vec (int)): bool {
    LenVec(v) >= LenVec(suffix) &&
    (forall i: int:: InRangeVec(suffix, i) ==> $IsEqual'u8'(ReadVec(v, LenVec(v) - LenVec(suffix) + i), ReadVec(suffix, i)))
}

// Not inlined.
function $IsValid'vec'u8''(v: Vec (int)): bool {
    $IsValid'u64'(LenVec(v)) &&
    (forall i: int:: InRangeVec(v, i) ==> $IsValid'u8'(ReadVec(v, i)))
}


function {:inline} $ContainsVec'u8'(v: Vec (int), e: int): bool {
    (exists i: int :: $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'u8'(ReadVec(v, i), e))
}

function $IndexOfVec'u8'(v: Vec (int), e: int): int;
axiom (forall v: Vec (int), e: int:: {$IndexOfVec'u8'(v, e)}
    (var i := $IndexOfVec'u8'(v, e);
     if (!$ContainsVec'u8'(v, e)) then i == -1
     else $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'u8'(ReadVec(v, i), e) &&
        (forall j: int :: $IsValid'u64'(j) && j >= 0 && j < i ==> !$IsEqual'u8'(ReadVec(v, j), e))));


function {:inline} $RangeVec'u8'(v: Vec (int)): $Range {
    $Range(0, LenVec(v))
}


function {:inline} $EmptyVec'u8'(): Vec (int) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_empty'u8'() returns (v: Vec (int)) {
    v := EmptyVec();
}

function {:inline} $1_vector_$empty'u8'(): Vec (int) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_is_empty'u8'(v: Vec (int)) returns (b: bool) {
    b := IsEmptyVec(v);
}

procedure {:inline 1} $1_vector_push_back'u8'(m: $Mutation (Vec (int)), val: int) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ExtendVec($Dereference(m), val));
}

function {:inline} $1_vector_$push_back'u8'(v: Vec (int), val: int): Vec (int) {
    ExtendVec(v, val)
}

procedure {:inline 1} $1_vector_pop_back'u8'(m: $Mutation (Vec (int))) returns (e: int, m': $Mutation (Vec (int))) {
    var v: Vec (int);
    var len: int;
    v := $Dereference(m);
    len := LenVec(v);
    if (len == 0) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, len-1);
    m' := $UpdateMutation(m, RemoveVec(v));
}

procedure {:inline 1} $1_vector_append'u8'(m: $Mutation (Vec (int)), other: Vec (int)) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), other));
}

procedure {:inline 1} $1_vector_reverse'u8'(m: $Mutation (Vec (int))) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ReverseVec($Dereference(m)));
}

procedure {:inline 1} $1_vector_reverse_append'u8'(m: $Mutation (Vec (int)), other: Vec (int)) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), ReverseVec(other)));
}

procedure {:inline 1} $1_vector_trim_reverse'u8'(m: $Mutation (Vec (int)), new_len: int) returns (v: (Vec (int)), m': $Mutation (Vec (int))) {
    var len: int;
    v := $Dereference(m);
    if (LenVec(v) < new_len) {
        call $ExecFailureAbort();
        return;
    }
    v := SliceVec(v, new_len, LenVec(v));
    v := ReverseVec(v);
    m' := $UpdateMutation(m, SliceVec($Dereference(m), 0, new_len));
}

procedure {:inline 1} $1_vector_trim'u8'(m: $Mutation (Vec (int)), new_len: int) returns (v: (Vec (int)), m': $Mutation (Vec (int))) {
    var len: int;
    v := $Dereference(m);
    if (LenVec(v) < new_len) {
        call $ExecFailureAbort();
        return;
    }
    v := SliceVec(v, new_len, LenVec(v));
    m' := $UpdateMutation(m, SliceVec($Dereference(m), 0, new_len));
}

procedure {:inline 1} $1_vector_reverse_slice'u8'(m: $Mutation (Vec (int)), left: int, right: int) returns (m': $Mutation (Vec (int))) {
    var left_vec: Vec (int);
    var mid_vec: Vec (int);
    var right_vec: Vec (int);
    var v: Vec (int);
    if (left > right) {
        call $ExecFailureAbort();
        return;
    }
    if (left == right) {
        m' := m;
        return;
    }
    v := $Dereference(m);
    if (!(right >= 0 && right <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    left_vec := SliceVec(v, 0, left);
    right_vec := SliceVec(v, right, LenVec(v));
    mid_vec := ReverseVec(SliceVec(v, left, right));
    m' := $UpdateMutation(m, ConcatVec(left_vec, ConcatVec(mid_vec, right_vec)));
}

procedure {:inline 1} $1_vector_rotate'u8'(m: $Mutation (Vec (int)), rot: int) returns (n: int, m': $Mutation (Vec (int))) {
    var v: Vec (int);
    var len: int;
    var left_vec: Vec (int);
    var right_vec: Vec (int);
    v := $Dereference(m);
    if (!(rot >= 0 && rot <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    left_vec := SliceVec(v, 0, rot);
    right_vec := SliceVec(v, rot, LenVec(v));
    m' := $UpdateMutation(m, ConcatVec(right_vec, left_vec));
    n := LenVec(v) - rot;
}

procedure {:inline 1} $1_vector_rotate_slice'u8'(m: $Mutation (Vec (int)), left: int, rot: int, right: int) returns (n: int, m': $Mutation (Vec (int))) {
    var left_vec: Vec (int);
    var mid_vec: Vec (int);
    var right_vec: Vec (int);
    var mid_left_vec: Vec (int);
    var mid_right_vec: Vec (int);
    var v: Vec (int);
    v := $Dereference(m);
    if (!(left <= rot && rot <= right)) {
        call $ExecFailureAbort();
        return;
    }
    if (!(right >= 0 && right <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    v := $Dereference(m);
    left_vec := SliceVec(v, 0, left);
    right_vec := SliceVec(v, right, LenVec(v));
    mid_left_vec := SliceVec(v, left, rot);
    mid_right_vec := SliceVec(v, rot, right);
    mid_vec := ConcatVec(mid_right_vec, mid_left_vec);
    m' := $UpdateMutation(m, ConcatVec(left_vec, ConcatVec(mid_vec, right_vec)));
    n := left + (right - rot);
}

procedure {:inline 1} $1_vector_insert'u8'(m: $Mutation (Vec (int)), i: int, e: int) returns (m': $Mutation (Vec (int))) {
    var left_vec: Vec (int);
    var right_vec: Vec (int);
    var v: Vec (int);
    v := $Dereference(m);
    if (!(i >= 0 && i <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    if (i == LenVec(v)) {
        m' := $UpdateMutation(m, ExtendVec(v, e));
    } else {
        left_vec := ExtendVec(SliceVec(v, 0, i), e);
        right_vec := SliceVec(v, i, LenVec(v));
        m' := $UpdateMutation(m, ConcatVec(left_vec, right_vec));
    }
}

procedure {:inline 1} $1_vector_length'u8'(v: Vec (int)) returns (l: int) {
    l := LenVec(v);
}

function {:inline} $1_vector_$length'u8'(v: Vec (int)): int {
    LenVec(v)
}

procedure {:inline 1} $1_vector_borrow'u8'(v: Vec (int), i: int) returns (dst: int) {
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    dst := ReadVec(v, i);
}

function {:inline} $1_vector_$borrow'u8'(v: Vec (int), i: int): int {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_borrow_mut'u8'(m: $Mutation (Vec (int)), index: int)
returns (dst: $Mutation (int), m': $Mutation (Vec (int)))
{
    var v: Vec (int);
    v := $Dereference(m);
    if (!InRangeVec(v, index)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mutation(m->l, ExtendVec(m->p, index), ReadVec(v, index));
    m' := m;
}

function {:inline} $1_vector_$borrow_mut'u8'(v: Vec (int), i: int): int {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_destroy_empty'u8'(v: Vec (int)) {
    if (!IsEmptyVec(v)) {
      call $ExecFailureAbort();
    }
}

procedure {:inline 1} $1_vector_swap'u8'(m: $Mutation (Vec (int)), i: int, j: int) returns (m': $Mutation (Vec (int)))
{
    var v: Vec (int);
    v := $Dereference(m);
    if (!InRangeVec(v, i) || !InRangeVec(v, j)) {
        call $ExecFailureAbort();
        return;
    }
    m' := $UpdateMutation(m, SwapVec(v, i, j));
}

function {:inline} $1_vector_$swap'u8'(v: Vec (int), i: int, j: int): Vec (int) {
    SwapVec(v, i, j)
}

procedure {:inline 1} $1_vector_remove'u8'(m: $Mutation (Vec (int)), i: int) returns (e: int, m': $Mutation (Vec (int)))
{
    var v: Vec (int);

    v := $Dereference(m);

    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveAtVec(v, i));
}

procedure {:inline 1} $1_vector_swap_remove'u8'(m: $Mutation (Vec (int)), i: int) returns (e: int, m': $Mutation (Vec (int)))
{
    var len: int;
    var v: Vec (int);

    v := $Dereference(m);
    len := LenVec(v);
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveVec(SwapVec(v, i, len-1)));
}

procedure {:inline 1} $1_vector_contains'u8'(v: Vec (int), e: int) returns (res: bool)  {
    res := $ContainsVec'u8'(v, e);
}

procedure {:inline 1}
$1_vector_index_of'u8'(v: Vec (int), e: int) returns (res1: bool, res2: int) {
    res2 := $IndexOfVec'u8'(v, e);
    if (res2 >= 0) {
        res1 := true;
    } else {
        res1 := false;
        res2 := 0;
    }
}


// ----------------------------------------------------------------------------------
// Native Vector implementation for element type `bv8`

// Not inlined. It appears faster this way.
function $IsEqual'vec'bv8''(v1: Vec (bv8), v2: Vec (bv8)): bool {
    LenVec(v1) == LenVec(v2) &&
    (forall i: int:: InRangeVec(v1, i) ==> $IsEqual'bv8'(ReadVec(v1, i), ReadVec(v2, i)))
}

// Not inlined.
function $IsPrefix'vec'bv8''(v: Vec (bv8), prefix: Vec (bv8)): bool {
    LenVec(v) >= LenVec(prefix) &&
    (forall i: int:: InRangeVec(prefix, i) ==> $IsEqual'bv8'(ReadVec(v, i), ReadVec(prefix, i)))
}

// Not inlined.
function $IsSuffix'vec'bv8''(v: Vec (bv8), suffix: Vec (bv8)): bool {
    LenVec(v) >= LenVec(suffix) &&
    (forall i: int:: InRangeVec(suffix, i) ==> $IsEqual'bv8'(ReadVec(v, LenVec(v) - LenVec(suffix) + i), ReadVec(suffix, i)))
}

// Not inlined.
function $IsValid'vec'bv8''(v: Vec (bv8)): bool {
    $IsValid'u64'(LenVec(v)) &&
    (forall i: int:: InRangeVec(v, i) ==> $IsValid'bv8'(ReadVec(v, i)))
}


function {:inline} $ContainsVec'bv8'(v: Vec (bv8), e: bv8): bool {
    (exists i: int :: $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'bv8'(ReadVec(v, i), e))
}

function $IndexOfVec'bv8'(v: Vec (bv8), e: bv8): int;
axiom (forall v: Vec (bv8), e: bv8:: {$IndexOfVec'bv8'(v, e)}
    (var i := $IndexOfVec'bv8'(v, e);
     if (!$ContainsVec'bv8'(v, e)) then i == -1
     else $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'bv8'(ReadVec(v, i), e) &&
        (forall j: int :: $IsValid'u64'(j) && j >= 0 && j < i ==> !$IsEqual'bv8'(ReadVec(v, j), e))));


function {:inline} $RangeVec'bv8'(v: Vec (bv8)): $Range {
    $Range(0, LenVec(v))
}


function {:inline} $EmptyVec'bv8'(): Vec (bv8) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_empty'bv8'() returns (v: Vec (bv8)) {
    v := EmptyVec();
}

function {:inline} $1_vector_$empty'bv8'(): Vec (bv8) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_is_empty'bv8'(v: Vec (bv8)) returns (b: bool) {
    b := IsEmptyVec(v);
}

procedure {:inline 1} $1_vector_push_back'bv8'(m: $Mutation (Vec (bv8)), val: bv8) returns (m': $Mutation (Vec (bv8))) {
    m' := $UpdateMutation(m, ExtendVec($Dereference(m), val));
}

function {:inline} $1_vector_$push_back'bv8'(v: Vec (bv8), val: bv8): Vec (bv8) {
    ExtendVec(v, val)
}

procedure {:inline 1} $1_vector_pop_back'bv8'(m: $Mutation (Vec (bv8))) returns (e: bv8, m': $Mutation (Vec (bv8))) {
    var v: Vec (bv8);
    var len: int;
    v := $Dereference(m);
    len := LenVec(v);
    if (len == 0) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, len-1);
    m' := $UpdateMutation(m, RemoveVec(v));
}

procedure {:inline 1} $1_vector_append'bv8'(m: $Mutation (Vec (bv8)), other: Vec (bv8)) returns (m': $Mutation (Vec (bv8))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), other));
}

procedure {:inline 1} $1_vector_reverse'bv8'(m: $Mutation (Vec (bv8))) returns (m': $Mutation (Vec (bv8))) {
    m' := $UpdateMutation(m, ReverseVec($Dereference(m)));
}

procedure {:inline 1} $1_vector_reverse_append'bv8'(m: $Mutation (Vec (bv8)), other: Vec (bv8)) returns (m': $Mutation (Vec (bv8))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), ReverseVec(other)));
}

procedure {:inline 1} $1_vector_trim_reverse'bv8'(m: $Mutation (Vec (bv8)), new_len: int) returns (v: (Vec (bv8)), m': $Mutation (Vec (bv8))) {
    var len: int;
    v := $Dereference(m);
    if (LenVec(v) < new_len) {
        call $ExecFailureAbort();
        return;
    }
    v := SliceVec(v, new_len, LenVec(v));
    v := ReverseVec(v);
    m' := $UpdateMutation(m, SliceVec($Dereference(m), 0, new_len));
}

procedure {:inline 1} $1_vector_trim'bv8'(m: $Mutation (Vec (bv8)), new_len: int) returns (v: (Vec (bv8)), m': $Mutation (Vec (bv8))) {
    var len: int;
    v := $Dereference(m);
    if (LenVec(v) < new_len) {
        call $ExecFailureAbort();
        return;
    }
    v := SliceVec(v, new_len, LenVec(v));
    m' := $UpdateMutation(m, SliceVec($Dereference(m), 0, new_len));
}

procedure {:inline 1} $1_vector_reverse_slice'bv8'(m: $Mutation (Vec (bv8)), left: int, right: int) returns (m': $Mutation (Vec (bv8))) {
    var left_vec: Vec (bv8);
    var mid_vec: Vec (bv8);
    var right_vec: Vec (bv8);
    var v: Vec (bv8);
    if (left > right) {
        call $ExecFailureAbort();
        return;
    }
    if (left == right) {
        m' := m;
        return;
    }
    v := $Dereference(m);
    if (!(right >= 0 && right <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    left_vec := SliceVec(v, 0, left);
    right_vec := SliceVec(v, right, LenVec(v));
    mid_vec := ReverseVec(SliceVec(v, left, right));
    m' := $UpdateMutation(m, ConcatVec(left_vec, ConcatVec(mid_vec, right_vec)));
}

procedure {:inline 1} $1_vector_rotate'bv8'(m: $Mutation (Vec (bv8)), rot: int) returns (n: int, m': $Mutation (Vec (bv8))) {
    var v: Vec (bv8);
    var len: int;
    var left_vec: Vec (bv8);
    var right_vec: Vec (bv8);
    v := $Dereference(m);
    if (!(rot >= 0 && rot <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    left_vec := SliceVec(v, 0, rot);
    right_vec := SliceVec(v, rot, LenVec(v));
    m' := $UpdateMutation(m, ConcatVec(right_vec, left_vec));
    n := LenVec(v) - rot;
}

procedure {:inline 1} $1_vector_rotate_slice'bv8'(m: $Mutation (Vec (bv8)), left: int, rot: int, right: int) returns (n: int, m': $Mutation (Vec (bv8))) {
    var left_vec: Vec (bv8);
    var mid_vec: Vec (bv8);
    var right_vec: Vec (bv8);
    var mid_left_vec: Vec (bv8);
    var mid_right_vec: Vec (bv8);
    var v: Vec (bv8);
    v := $Dereference(m);
    if (!(left <= rot && rot <= right)) {
        call $ExecFailureAbort();
        return;
    }
    if (!(right >= 0 && right <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    v := $Dereference(m);
    left_vec := SliceVec(v, 0, left);
    right_vec := SliceVec(v, right, LenVec(v));
    mid_left_vec := SliceVec(v, left, rot);
    mid_right_vec := SliceVec(v, rot, right);
    mid_vec := ConcatVec(mid_right_vec, mid_left_vec);
    m' := $UpdateMutation(m, ConcatVec(left_vec, ConcatVec(mid_vec, right_vec)));
    n := left + (right - rot);
}

procedure {:inline 1} $1_vector_insert'bv8'(m: $Mutation (Vec (bv8)), i: int, e: bv8) returns (m': $Mutation (Vec (bv8))) {
    var left_vec: Vec (bv8);
    var right_vec: Vec (bv8);
    var v: Vec (bv8);
    v := $Dereference(m);
    if (!(i >= 0 && i <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    if (i == LenVec(v)) {
        m' := $UpdateMutation(m, ExtendVec(v, e));
    } else {
        left_vec := ExtendVec(SliceVec(v, 0, i), e);
        right_vec := SliceVec(v, i, LenVec(v));
        m' := $UpdateMutation(m, ConcatVec(left_vec, right_vec));
    }
}

procedure {:inline 1} $1_vector_length'bv8'(v: Vec (bv8)) returns (l: int) {
    l := LenVec(v);
}

function {:inline} $1_vector_$length'bv8'(v: Vec (bv8)): int {
    LenVec(v)
}

procedure {:inline 1} $1_vector_borrow'bv8'(v: Vec (bv8), i: int) returns (dst: bv8) {
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    dst := ReadVec(v, i);
}

function {:inline} $1_vector_$borrow'bv8'(v: Vec (bv8), i: int): bv8 {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_borrow_mut'bv8'(m: $Mutation (Vec (bv8)), index: int)
returns (dst: $Mutation (bv8), m': $Mutation (Vec (bv8)))
{
    var v: Vec (bv8);
    v := $Dereference(m);
    if (!InRangeVec(v, index)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mutation(m->l, ExtendVec(m->p, index), ReadVec(v, index));
    m' := m;
}

function {:inline} $1_vector_$borrow_mut'bv8'(v: Vec (bv8), i: int): bv8 {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_destroy_empty'bv8'(v: Vec (bv8)) {
    if (!IsEmptyVec(v)) {
      call $ExecFailureAbort();
    }
}

procedure {:inline 1} $1_vector_swap'bv8'(m: $Mutation (Vec (bv8)), i: int, j: int) returns (m': $Mutation (Vec (bv8)))
{
    var v: Vec (bv8);
    v := $Dereference(m);
    if (!InRangeVec(v, i) || !InRangeVec(v, j)) {
        call $ExecFailureAbort();
        return;
    }
    m' := $UpdateMutation(m, SwapVec(v, i, j));
}

function {:inline} $1_vector_$swap'bv8'(v: Vec (bv8), i: int, j: int): Vec (bv8) {
    SwapVec(v, i, j)
}

procedure {:inline 1} $1_vector_remove'bv8'(m: $Mutation (Vec (bv8)), i: int) returns (e: bv8, m': $Mutation (Vec (bv8)))
{
    var v: Vec (bv8);

    v := $Dereference(m);

    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveAtVec(v, i));
}

procedure {:inline 1} $1_vector_swap_remove'bv8'(m: $Mutation (Vec (bv8)), i: int) returns (e: bv8, m': $Mutation (Vec (bv8)))
{
    var len: int;
    var v: Vec (bv8);

    v := $Dereference(m);
    len := LenVec(v);
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveVec(SwapVec(v, i, len-1)));
}

procedure {:inline 1} $1_vector_contains'bv8'(v: Vec (bv8), e: bv8) returns (res: bool)  {
    res := $ContainsVec'bv8'(v, e);
}

procedure {:inline 1}
$1_vector_index_of'bv8'(v: Vec (bv8), e: bv8) returns (res1: bool, res2: int) {
    res2 := $IndexOfVec'bv8'(v, e);
    if (res2 >= 0) {
        res1 := true;
    } else {
        res1 := false;
        res2 := 0;
    }
}


// ==================================================================================
// Native Table

// ----------------------------------------------------------------------------------
// Native Table key encoding for type `u64`

function $EncodeKey'u64'(k: int): int;
axiom (
  forall k1, k2: int :: {$EncodeKey'u64'(k1), $EncodeKey'u64'(k2)}
    $IsEqual'u64'(k1, k2) <==> $EncodeKey'u64'(k1) == $EncodeKey'u64'(k2)
);


// ----------------------------------------------------------------------------------
// Native Table implementation for type `(u64,$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task)`

function $IsEqual'$1_table_Table'u64_$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task''(t1: Table int ($747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task), t2: Table int ($747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task)): bool {
    LenTable(t1) == LenTable(t2) &&
    (forall k: int :: ContainsTable(t1, k) <==> ContainsTable(t2, k)) &&
    (forall k: int :: ContainsTable(t1, k) ==> GetTable(t1, k) == GetTable(t2, k)) &&
    (forall k: int :: ContainsTable(t2, k) ==> GetTable(t1, k) == GetTable(t2, k))
}

// Not inlined.
function $IsValid'$1_table_Table'u64_$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task''(t: Table int ($747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task)): bool {
    $IsValid'u64'(LenTable(t)) &&
    (forall i: int:: ContainsTable(t, i) ==> $IsValid'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task'(GetTable(t, i)))
}
procedure {:inline 2} $1_table_new'u64_$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task'() returns (v: Table int ($747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task)) {
    v := EmptyTable();
}
procedure {:inline 2} $1_table_destroy'u64_$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task'(t: Table int ($747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task)) {
    if (LenTable(t) != 0) {
        call $Abort($StdError(1/*INVALID_STATE*/, 102/*ENOT_EMPTY*/));
    }
}
procedure {:inline 2} $1_table_contains'u64_$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task'(t: (Table int ($747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task)), k: int) returns (r: bool) {
    r := ContainsTable(t, $EncodeKey'u64'(k));
}
procedure {:inline 2} $1_table_add'u64_$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task'(m: $Mutation (Table int ($747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task)), k: int, v: $747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task) returns (m': $Mutation(Table int ($747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task))) {
    var enc_k: int;
    var t: Table int ($747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task);
    enc_k := $EncodeKey'u64'(k);
    t := $Dereference(m);
    if (ContainsTable(t, enc_k)) {
        call $Abort($StdError(7/*INVALID_ARGUMENTS*/, 100/*EALREADY_EXISTS*/));
    } else {
        m' := $UpdateMutation(m, AddTable(t, enc_k, v));
    }
}
procedure {:inline 2} $1_table_upsert'u64_$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task'(m: $Mutation (Table int ($747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task)), k: int, v: $747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task) returns (m': $Mutation(Table int ($747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task))) {
    var enc_k: int;
    var t: Table int ($747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task);
    enc_k := $EncodeKey'u64'(k);
    t := $Dereference(m);
    if (ContainsTable(t, enc_k)) {
        m' := $UpdateMutation(m, UpdateTable(t, enc_k, v));
    } else {
        m' := $UpdateMutation(m, AddTable(t, enc_k, v));
    }
}
procedure {:inline 2} $1_table_remove'u64_$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task'(m: $Mutation (Table int ($747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task)), k: int)
returns (v: $747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task, m': $Mutation(Table int ($747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task))) {
    var enc_k: int;
    var t: Table int ($747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task);
    enc_k := $EncodeKey'u64'(k);
    t := $Dereference(m);
    if (!ContainsTable(t, enc_k)) {
        call $Abort($StdError(7/*INVALID_ARGUMENTS*/, 101/*ENOT_FOUND*/));
    } else {
        v := GetTable(t, enc_k);
        m' := $UpdateMutation(m, RemoveTable(t, enc_k));
    }
}
procedure {:inline 2} $1_table_borrow'u64_$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task'(t: Table int ($747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task), k: int) returns (v: $747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task) {
    var enc_k: int;
    enc_k := $EncodeKey'u64'(k);
    if (!ContainsTable(t, enc_k)) {
        call $Abort($StdError(7/*INVALID_ARGUMENTS*/, 101/*ENOT_FOUND*/));
    } else {
        v := GetTable(t, $EncodeKey'u64'(k));
    }
}
procedure {:inline 2} $1_table_borrow_mut'u64_$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task'(m: $Mutation (Table int ($747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task)), k: int)
returns (dst: $Mutation ($747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task), m': $Mutation (Table int ($747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task))) {
    var enc_k: int;
    var t: Table int ($747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task);
    enc_k := $EncodeKey'u64'(k);
    t := $Dereference(m);
    if (!ContainsTable(t, enc_k)) {
        call $Abort($StdError(7/*INVALID_ARGUMENTS*/, 101/*ENOT_FOUND*/));
    } else {
        dst := $Mutation(m->l, ExtendVec(m->p, enc_k), GetTable(t, enc_k));
        m' := m;
    }
}
procedure {:inline 2} $1_table_borrow_mut_with_default'u64_$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task'(m: $Mutation (Table int ($747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task)), k: int, default: $747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task)
returns (dst: $Mutation ($747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task), m': $Mutation (Table int ($747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task))) {
    var enc_k: int;
    var t: Table int ($747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task);
    var t': Table int ($747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task);
    enc_k := $EncodeKey'u64'(k);
    t := $Dereference(m);
    if (!ContainsTable(t, enc_k)) {
        m' := $UpdateMutation(m, AddTable(t, enc_k, default));
        t' := $Dereference(m');
        dst := $Mutation(m'->l, ExtendVec(m'->p, enc_k), GetTable(t', enc_k));
    } else {
        dst := $Mutation(m->l, ExtendVec(m->p, enc_k), GetTable(t, enc_k));
        m' := m;
    }
}
function {:inline} $1_table_spec_contains'u64_$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task'(t: (Table int ($747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task)), k: int): bool {
    ContainsTable(t, $EncodeKey'u64'(k))
}
function {:inline} $1_table_spec_set'u64_$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task'(t: Table int ($747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task), k: int, v: $747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task): Table int ($747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task) {
    (var enc_k := $EncodeKey'u64'(k);
    if (ContainsTable(t, enc_k)) then
        UpdateTable(t, enc_k, v)
    else
        AddTable(t, enc_k, v))
}
function {:inline} $1_table_spec_remove'u64_$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task'(t: Table int ($747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task), k: int): Table int ($747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task) {
    RemoveTable(t, $EncodeKey'u64'(k))
}
function {:inline} $1_table_spec_get'u64_$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task'(t: Table int ($747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task), k: int): $747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task {
    GetTable(t, $EncodeKey'u64'(k))
}



// ==================================================================================
// Native Hash

// Hash is modeled as an otherwise uninterpreted injection.
// In truth, it is not an injection since the domain has greater cardinality
// (arbitrary length vectors) than the co-domain (vectors of length 32).  But it is
// common to assume in code there are no hash collisions in practice.  Fortunately,
// Boogie is not smart enough to recognized that there is an inconsistency.
// FIXME: If we were using a reliable extensional theory of arrays, and if we could use ==
// instead of $IsEqual, we might be able to avoid so many quantified formulas by
// using a sha2_inverse function in the ensures conditions of Hash_sha2_256 to
// assert that sha2/3 are injections without using global quantified axioms.


function $1_hash_sha2(val: Vec int): Vec int;

// This says that Hash_sha2 is bijective.
axiom (forall v1,v2: Vec int :: {$1_hash_sha2(v1), $1_hash_sha2(v2)}
       $IsEqual'vec'u8''(v1, v2) <==> $IsEqual'vec'u8''($1_hash_sha2(v1), $1_hash_sha2(v2)));

procedure $1_hash_sha2_256(val: Vec int) returns (res: Vec int);
ensures res == $1_hash_sha2(val);     // returns Hash_sha2 Value
ensures $IsValid'vec'u8''(res);    // result is a legal vector of U8s.
ensures LenVec(res) == 32;               // result is 32 bytes.

// Spec version of Move native function.
function {:inline} $1_hash_$sha2_256(val: Vec int): Vec int {
    $1_hash_sha2(val)
}

// similarly for Hash_sha3
function $1_hash_sha3(val: Vec int): Vec int;

axiom (forall v1,v2: Vec int :: {$1_hash_sha3(v1), $1_hash_sha3(v2)}
       $IsEqual'vec'u8''(v1, v2) <==> $IsEqual'vec'u8''($1_hash_sha3(v1), $1_hash_sha3(v2)));

procedure $1_hash_sha3_256(val: Vec int) returns (res: Vec int);
ensures res == $1_hash_sha3(val);     // returns Hash_sha3 Value
ensures $IsValid'vec'u8''(res);    // result is a legal vector of U8s.
ensures LenVec(res) == 32;               // result is 32 bytes.

// Spec version of Move native function.
function {:inline} $1_hash_$sha3_256(val: Vec int): Vec int {
    $1_hash_sha3(val)
}

// ==================================================================================
// Native string

// TODO: correct implementation of strings

procedure {:inline 1} $1_string_internal_check_utf8(x: Vec int) returns (r: bool) {
}

procedure {:inline 1} $1_string_internal_sub_string(x: Vec int, i: int, j: int) returns (r: Vec int) {
}

procedure {:inline 1} $1_string_internal_index_of(x: Vec int, y: Vec int) returns (r: int) {
}

procedure {:inline 1} $1_string_internal_is_char_boundary(x: Vec int, i: int) returns (r: bool) {
}




// ==================================================================================
// Native diem_account

procedure {:inline 1} $1_DiemAccount_create_signer(
  addr: int
) returns (signer: $signer) {
    // A signer is currently identical to an address.
    signer := $signer(addr);
}

procedure {:inline 1} $1_DiemAccount_destroy_signer(
  signer: $signer
) {
  return;
}

// ==================================================================================
// Native account

procedure {:inline 1} $1_Account_create_signer(
  addr: int
) returns (signer: $signer) {
    // A signer is currently identical to an address.
    signer := $signer(addr);
}

// ==================================================================================
// Native Signer

datatype $signer {
    $signer($addr: int)
}
function {:inline} $IsValid'signer'(s: $signer): bool {
    $IsValid'address'(s->$addr)
}
function {:inline} $IsEqual'signer'(s1: $signer, s2: $signer): bool {
    s1 == s2
}

procedure {:inline 1} $1_signer_borrow_address(signer: $signer) returns (res: int) {
    res := signer->$addr;
}

function {:inline} $1_signer_$borrow_address(signer: $signer): int
{
    signer->$addr
}

function $1_signer_is_txn_signer(s: $signer): bool;

function $1_signer_is_txn_signer_addr(a: int): bool;


// ==================================================================================
// Native signature

// Signature related functionality is handled via uninterpreted functions. This is sound
// currently because we verify every code path based on signature verification with
// an arbitrary interpretation.

function $1_Signature_$ed25519_validate_pubkey(public_key: Vec int): bool;
function $1_Signature_$ed25519_verify(signature: Vec int, public_key: Vec int, message: Vec int): bool;

// Needed because we do not have extensional equality:
axiom (forall k1, k2: Vec int ::
    {$1_Signature_$ed25519_validate_pubkey(k1), $1_Signature_$ed25519_validate_pubkey(k2)}
    $IsEqual'vec'u8''(k1, k2) ==> $1_Signature_$ed25519_validate_pubkey(k1) == $1_Signature_$ed25519_validate_pubkey(k2));
axiom (forall s1, s2, k1, k2, m1, m2: Vec int ::
    {$1_Signature_$ed25519_verify(s1, k1, m1), $1_Signature_$ed25519_verify(s2, k2, m2)}
    $IsEqual'vec'u8''(s1, s2) && $IsEqual'vec'u8''(k1, k2) && $IsEqual'vec'u8''(m1, m2)
    ==> $1_Signature_$ed25519_verify(s1, k1, m1) == $1_Signature_$ed25519_verify(s2, k2, m2));


procedure {:inline 1} $1_Signature_ed25519_validate_pubkey(public_key: Vec int) returns (res: bool) {
    res := $1_Signature_$ed25519_validate_pubkey(public_key);
}

procedure {:inline 1} $1_Signature_ed25519_verify(
        signature: Vec int, public_key: Vec int, message: Vec int) returns (res: bool) {
    res := $1_Signature_$ed25519_verify(signature, public_key, message);
}


// ==================================================================================
// Native bcs::serialize


// ==================================================================================
// Native Event module



procedure {:inline 1} $InitEventStore() {
}

// ============================================================================================
// Type Reflection on Type Parameters

datatype $TypeParamInfo {
    $TypeParamBool(),
    $TypeParamU8(),
    $TypeParamU16(),
    $TypeParamU32(),
    $TypeParamU64(),
    $TypeParamU128(),
    $TypeParamU256(),
    $TypeParamAddress(),
    $TypeParamSigner(),
    $TypeParamVector(e: $TypeParamInfo),
    $TypeParamStruct(a: int, m: Vec int, s: Vec int)
}



//==================================
// Begin Translation

function $TypeName(t: $TypeParamInfo): Vec int;
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} t is $TypeParamBool ==> $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 98][1 := 111][2 := 111][3 := 108], 4)));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 98][1 := 111][2 := 111][3 := 108], 4)) ==> t is $TypeParamBool);
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} t is $TypeParamU8 ==> $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 56], 2)));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 56], 2)) ==> t is $TypeParamU8);
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} t is $TypeParamU16 ==> $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 49][2 := 54], 3)));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 49][2 := 54], 3)) ==> t is $TypeParamU16);
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} t is $TypeParamU32 ==> $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 51][2 := 50], 3)));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 51][2 := 50], 3)) ==> t is $TypeParamU32);
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} t is $TypeParamU64 ==> $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 54][2 := 52], 3)));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 54][2 := 52], 3)) ==> t is $TypeParamU64);
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} t is $TypeParamU128 ==> $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 49][2 := 50][3 := 56], 4)));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 49][2 := 50][3 := 56], 4)) ==> t is $TypeParamU128);
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} t is $TypeParamU256 ==> $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 50][2 := 53][3 := 54], 4)));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 50][2 := 53][3 := 54], 4)) ==> t is $TypeParamU256);
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} t is $TypeParamAddress ==> $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 97][1 := 100][2 := 100][3 := 114][4 := 101][5 := 115][6 := 115], 7)));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 97][1 := 100][2 := 100][3 := 114][4 := 101][5 := 115][6 := 115], 7)) ==> t is $TypeParamAddress);
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} t is $TypeParamSigner ==> $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 115][1 := 105][2 := 103][3 := 110][4 := 101][5 := 114], 6)));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 115][1 := 105][2 := 103][3 := 110][4 := 101][5 := 114], 6)) ==> t is $TypeParamSigner);
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} t is $TypeParamVector ==> $IsEqual'vec'u8''($TypeName(t), ConcatVec(ConcatVec(Vec(DefaultVecMap()[0 := 118][1 := 101][2 := 99][3 := 116][4 := 111][5 := 114][6 := 60], 7), $TypeName(t->e)), Vec(DefaultVecMap()[0 := 62], 1))));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} ($IsPrefix'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 118][1 := 101][2 := 99][3 := 116][4 := 111][5 := 114][6 := 60], 7)) && $IsSuffix'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 62], 1))) ==> t is $TypeParamVector);
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} t is $TypeParamStruct ==> $IsEqual'vec'u8''($TypeName(t), ConcatVec(ConcatVec(ConcatVec(ConcatVec(ConcatVec(Vec(DefaultVecMap()[0 := 48][1 := 120], 2), MakeVec1(t->a)), Vec(DefaultVecMap()[0 := 58][1 := 58], 2)), t->m), Vec(DefaultVecMap()[0 := 58][1 := 58], 2)), t->s)));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} $IsPrefix'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 48][1 := 120], 2)) ==> t is $TypeParamVector);


// Given Types for Type Parameters

type #0;
function {:inline} $IsEqual'#0'(x1: #0, x2: #0): bool { x1 == x2 }
function {:inline} $IsValid'#0'(x: #0): bool { true }
var #0_info: $TypeParamInfo;
var #0_$memory: $Memory #0;

// axiom at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:18:9+124, instance <bool>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'bool'(b1), $1_from_bcs_deserializable'bool'(b2)))));

// axiom at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:18:9+124, instance <u64>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'u64'(b1), $1_from_bcs_deserializable'u64'(b2)))));

// axiom at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:18:9+124, instance <u256>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'u256'(b1), $1_from_bcs_deserializable'u256'(b2)))));

// axiom at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:18:9+124, instance <address>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'address'(b1), $1_from_bcs_deserializable'address'(b2)))));

// axiom at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:18:9+124, instance <signer>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'signer'(b1), $1_from_bcs_deserializable'signer'(b2)))));

// axiom at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:18:9+124, instance <vector<u8>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'vec'u8''(b1), $1_from_bcs_deserializable'vec'u8''(b2)))));

// axiom at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:18:9+124, instance <vector<address>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'vec'address''(b1), $1_from_bcs_deserializable'vec'address''(b2)))));

// axiom at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:18:9+124, instance <vector<#0>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'vec'#0''(b1), $1_from_bcs_deserializable'vec'#0''(b2)))));

// axiom at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:18:9+124, instance <option::Option<address>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_option_Option'address''(b1), $1_from_bcs_deserializable'$1_option_Option'address''(b2)))));

// axiom at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:18:9+124, instance <string::String>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_string_String'(b1), $1_from_bcs_deserializable'$1_string_String'(b2)))));

// axiom at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:18:9+124, instance <type_info::TypeInfo>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_type_info_TypeInfo'(b1), $1_from_bcs_deserializable'$1_type_info_TypeInfo'(b2)))));

// axiom at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:18:9+124, instance <table::Table<u64, todolist::Task>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_table_Table'u64_$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task''(b1), $1_from_bcs_deserializable'$1_table_Table'u64_$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task''(b2)))));

// axiom at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:18:9+124, instance <guid::GUID>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_guid_GUID'(b1), $1_from_bcs_deserializable'$1_guid_GUID'(b2)))));

// axiom at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:18:9+124, instance <guid::ID>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_guid_ID'(b1), $1_from_bcs_deserializable'$1_guid_ID'(b2)))));

// axiom at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:18:9+124, instance <event::EventHandle<account::CoinRegisterEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_event_EventHandle'$1_account_CoinRegisterEvent''(b1), $1_from_bcs_deserializable'$1_event_EventHandle'$1_account_CoinRegisterEvent''(b2)))));

// axiom at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:18:9+124, instance <event::EventHandle<account::KeyRotationEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_event_EventHandle'$1_account_KeyRotationEvent''(b1), $1_from_bcs_deserializable'$1_event_EventHandle'$1_account_KeyRotationEvent''(b2)))));

// axiom at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:18:9+124, instance <event::EventHandle<todolist::Task>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_event_EventHandle'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task''(b1), $1_from_bcs_deserializable'$1_event_EventHandle'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task''(b2)))));

// axiom at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:18:9+124, instance <account::Account>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_account_Account'(b1), $1_from_bcs_deserializable'$1_account_Account'(b2)))));

// axiom at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:18:9+124, instance <account::CapabilityOffer<account::RotationCapability>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_account_CapabilityOffer'$1_account_RotationCapability''(b1), $1_from_bcs_deserializable'$1_account_CapabilityOffer'$1_account_RotationCapability''(b2)))));

// axiom at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:18:9+124, instance <account::CapabilityOffer<account::SignerCapability>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$1_account_CapabilityOffer'$1_account_SignerCapability''(b1), $1_from_bcs_deserializable'$1_account_CapabilityOffer'$1_account_SignerCapability''(b2)))));

// axiom at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:18:9+124, instance <todolist::Task>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task'(b1), $1_from_bcs_deserializable'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task'(b2)))));

// axiom at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:18:9+124, instance <todolist::TodoList>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList'(b1), $1_from_bcs_deserializable'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList'(b2)))));

// axiom at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:18:9+124, instance <#0>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserializable'#0'(b1), $1_from_bcs_deserializable'#0'(b2)))));

// axiom at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:21:9+118, instance <bool>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'bool'($1_from_bcs_deserialize'bool'(b1), $1_from_bcs_deserialize'bool'(b2)))));

// axiom at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:21:9+118, instance <u64>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'u64'($1_from_bcs_deserialize'u64'(b1), $1_from_bcs_deserialize'u64'(b2)))));

// axiom at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:21:9+118, instance <u256>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'u256'($1_from_bcs_deserialize'u256'(b1), $1_from_bcs_deserialize'u256'(b2)))));

// axiom at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:21:9+118, instance <address>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'address'($1_from_bcs_deserialize'address'(b1), $1_from_bcs_deserialize'address'(b2)))));

// axiom at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:21:9+118, instance <signer>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'signer'($1_from_bcs_deserialize'signer'(b1), $1_from_bcs_deserialize'signer'(b2)))));

// axiom at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:21:9+118, instance <vector<u8>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'vec'u8''($1_from_bcs_deserialize'vec'u8''(b1), $1_from_bcs_deserialize'vec'u8''(b2)))));

// axiom at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:21:9+118, instance <vector<address>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'vec'address''($1_from_bcs_deserialize'vec'address''(b1), $1_from_bcs_deserialize'vec'address''(b2)))));

// axiom at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:21:9+118, instance <vector<#0>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'vec'#0''($1_from_bcs_deserialize'vec'#0''(b1), $1_from_bcs_deserialize'vec'#0''(b2)))));

// axiom at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:21:9+118, instance <option::Option<address>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_option_Option'address''($1_from_bcs_deserialize'$1_option_Option'address''(b1), $1_from_bcs_deserialize'$1_option_Option'address''(b2)))));

// axiom at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:21:9+118, instance <string::String>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_string_String'($1_from_bcs_deserialize'$1_string_String'(b1), $1_from_bcs_deserialize'$1_string_String'(b2)))));

// axiom at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:21:9+118, instance <type_info::TypeInfo>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_type_info_TypeInfo'($1_from_bcs_deserialize'$1_type_info_TypeInfo'(b1), $1_from_bcs_deserialize'$1_type_info_TypeInfo'(b2)))));

// axiom at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:21:9+118, instance <table::Table<u64, todolist::Task>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_table_Table'u64_$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task''($1_from_bcs_deserialize'$1_table_Table'u64_$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task''(b1), $1_from_bcs_deserialize'$1_table_Table'u64_$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task''(b2)))));

// axiom at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:21:9+118, instance <guid::GUID>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_guid_GUID'($1_from_bcs_deserialize'$1_guid_GUID'(b1), $1_from_bcs_deserialize'$1_guid_GUID'(b2)))));

// axiom at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:21:9+118, instance <guid::ID>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_guid_ID'($1_from_bcs_deserialize'$1_guid_ID'(b1), $1_from_bcs_deserialize'$1_guid_ID'(b2)))));

// axiom at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:21:9+118, instance <event::EventHandle<account::CoinRegisterEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_event_EventHandle'$1_account_CoinRegisterEvent''($1_from_bcs_deserialize'$1_event_EventHandle'$1_account_CoinRegisterEvent''(b1), $1_from_bcs_deserialize'$1_event_EventHandle'$1_account_CoinRegisterEvent''(b2)))));

// axiom at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:21:9+118, instance <event::EventHandle<account::KeyRotationEvent>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_event_EventHandle'$1_account_KeyRotationEvent''($1_from_bcs_deserialize'$1_event_EventHandle'$1_account_KeyRotationEvent''(b1), $1_from_bcs_deserialize'$1_event_EventHandle'$1_account_KeyRotationEvent''(b2)))));

// axiom at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:21:9+118, instance <event::EventHandle<todolist::Task>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_event_EventHandle'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task''($1_from_bcs_deserialize'$1_event_EventHandle'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task''(b1), $1_from_bcs_deserialize'$1_event_EventHandle'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task''(b2)))));

// axiom at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:21:9+118, instance <account::Account>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_account_Account'($1_from_bcs_deserialize'$1_account_Account'(b1), $1_from_bcs_deserialize'$1_account_Account'(b2)))));

// axiom at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:21:9+118, instance <account::CapabilityOffer<account::RotationCapability>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_account_CapabilityOffer'$1_account_RotationCapability''($1_from_bcs_deserialize'$1_account_CapabilityOffer'$1_account_RotationCapability''(b1), $1_from_bcs_deserialize'$1_account_CapabilityOffer'$1_account_RotationCapability''(b2)))));

// axiom at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:21:9+118, instance <account::CapabilityOffer<account::SignerCapability>>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$1_account_CapabilityOffer'$1_account_SignerCapability''($1_from_bcs_deserialize'$1_account_CapabilityOffer'$1_account_SignerCapability''(b1), $1_from_bcs_deserialize'$1_account_CapabilityOffer'$1_account_SignerCapability''(b2)))));

// axiom at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:21:9+118, instance <todolist::Task>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task'($1_from_bcs_deserialize'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task'(b1), $1_from_bcs_deserialize'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task'(b2)))));

// axiom at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:21:9+118, instance <todolist::TodoList>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList'($1_from_bcs_deserialize'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList'(b1), $1_from_bcs_deserialize'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList'(b2)))));

// axiom at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:21:9+118, instance <#0>
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''(b1, b2) ==> $IsEqual'#0'($1_from_bcs_deserialize'#0'(b1), $1_from_bcs_deserialize'#0'(b2)))));

// axiom at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\hash.spec.move:8:9+113
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''($1_aptos_hash_spec_keccak256(b1), $1_aptos_hash_spec_keccak256(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\hash.spec.move:13:9+129
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''($1_aptos_hash_spec_sha2_512_internal(b1), $1_aptos_hash_spec_sha2_512_internal(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\hash.spec.move:18:9+129
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''($1_aptos_hash_spec_sha3_512_internal(b1), $1_aptos_hash_spec_sha3_512_internal(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\hash.spec.move:23:9+131
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''($1_aptos_hash_spec_ripemd160_internal(b1), $1_aptos_hash_spec_ripemd160_internal(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// axiom at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\hash.spec.move:28:9+135
axiom (forall b1: Vec (int), b2: Vec (int) :: $IsValid'vec'u8''(b1) ==> $IsValid'vec'u8''(b2) ==> (($IsEqual'vec'u8''($1_aptos_hash_spec_blake2b_256_internal(b1), $1_aptos_hash_spec_blake2b_256_internal(b2)) ==> $IsEqual'vec'u8''(b1, b2))));

// struct option::Option<address> at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\../move-stdlib\sources\option.move:7:5+81
datatype $1_option_Option'address' {
    $1_option_Option'address'($vec: Vec (int))
}
function {:inline} $Update'$1_option_Option'address''_vec(s: $1_option_Option'address', x: Vec (int)): $1_option_Option'address' {
    $1_option_Option'address'(x)
}
function $IsValid'$1_option_Option'address''(s: $1_option_Option'address'): bool {
    $IsValid'vec'address''(s->$vec)
}
function {:inline} $IsEqual'$1_option_Option'address''(s1: $1_option_Option'address', s2: $1_option_Option'address'): bool {
    $IsEqual'vec'address''(s1->$vec, s2->$vec)}

// struct string::String at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\../move-stdlib\sources\string.move:13:5+70
datatype $1_string_String {
    $1_string_String($bytes: Vec (int))
}
function {:inline} $Update'$1_string_String'_bytes(s: $1_string_String, x: Vec (int)): $1_string_String {
    $1_string_String(x)
}
function $IsValid'$1_string_String'(s: $1_string_String): bool {
    $IsValid'vec'u8''(s->$bytes)
}
function {:inline} $IsEqual'$1_string_String'(s1: $1_string_String, s2: $1_string_String): bool {
    $IsEqual'vec'u8''(s1->$bytes, s2->$bytes)}

// spec fun at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\../move-stdlib\sources\signer.move:12:5+77
function {:inline} $1_signer_$address_of(s: $signer): int {
    $1_signer_$borrow_address(s)
}

// fun signer::address_of [baseline] at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\../move-stdlib\sources\signer.move:12:5+77
procedure {:inline 1} $1_signer_address_of(_$t0: $signer) returns ($ret0: int)
{
    // declare local variables
    var $t1: int;
    var $t2: int;
    var $t0: $signer;
    var $temp_0'address': int;
    var $temp_0'signer': $signer;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[s]($t0) at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\../move-stdlib\sources\signer.move:12:5+1
    assume {:print "$at(13,395,396)"} true;
    assume {:print "$track_local(3,0,0):", $t0} $t0 == $t0;

    // $t1 := signer::borrow_address($t0) on_abort goto L2 with $t2 at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\../move-stdlib\sources\signer.move:13:10+17
    assume {:print "$at(13,449,466)"} true;
    call $t1 := $1_signer_borrow_address($t0);
    if ($abort_flag) {
        assume {:print "$at(13,449,466)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(3,0):", $t2} $t2 == $t2;
        goto L2;
    }

    // trace_return[0]($t1) at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\../move-stdlib\sources\signer.move:13:9+18
    assume {:print "$track_return(3,0,0):", $t1} $t1 == $t1;

    // label L1 at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\../move-stdlib\sources\signer.move:14:5+1
    assume {:print "$at(13,471,472)"} true;
L1:

    // return $t1 at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\../move-stdlib\sources\signer.move:14:5+1
    assume {:print "$at(13,471,472)"} true;
    $ret0 := $t1;
    return;

    // label L2 at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\../move-stdlib\sources\signer.move:14:5+1
L2:

    // abort($t2) at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\../move-stdlib\sources\signer.move:14:5+1
    assume {:print "$at(13,471,472)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun error::out_of_range [baseline] at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\../move-stdlib\sources\error.move:77:3+68
procedure {:inline 1} $1_error_out_of_range(_$t0: int) returns ($ret0: int)
{
    // declare local variables
    var $t1: int;
    var $t2: int;
    var $t3: int;
    var $t0: int;
    var $temp_0'u64': int;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[r]($t0) at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\../move-stdlib\sources\error.move:77:3+1
    assume {:print "$at(9,3161,3162)"} true;
    assume {:print "$track_local(4,8,0):", $t0} $t0 == $t0;

    // $t1 := 2 at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\../move-stdlib\sources\error.move:77:53+12
    $t1 := 2;
    assume $IsValid'u64'($t1);

    // assume Identical($t2, Shl($t1, 16)) at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\../move-stdlib\sources\error.move:69:5+29
    assume {:print "$at(9,2844,2873)"} true;
    assume ($t2 == $shlU64($t1, 16));

    // $t3 := opaque begin: error::canonical($t1, $t0) at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\../move-stdlib\sources\error.move:77:43+26
    assume {:print "$at(9,3201,3227)"} true;

    // assume WellFormed($t3) at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\../move-stdlib\sources\error.move:77:43+26
    assume $IsValid'u64'($t3);

    // assume Eq<u64>($t3, $t1) at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\../move-stdlib\sources\error.move:77:43+26
    assume $IsEqual'u64'($t3, $t1);

    // $t3 := opaque end: error::canonical($t1, $t0) at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\../move-stdlib\sources\error.move:77:43+26

    // trace_return[0]($t3) at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\../move-stdlib\sources\error.move:77:43+26
    assume {:print "$track_return(4,8,0):", $t3} $t3 == $t3;

    // label L1 at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\../move-stdlib\sources\error.move:77:70+1
L1:

    // return $t3 at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\../move-stdlib\sources\error.move:77:70+1
    assume {:print "$at(9,3228,3229)"} true;
    $ret0 := $t3;
    return;

}

// struct type_info::TypeInfo at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\type_info.move:17:5+145
datatype $1_type_info_TypeInfo {
    $1_type_info_TypeInfo($account_address: int, $module_name: Vec (int), $struct_name: Vec (int))
}
function {:inline} $Update'$1_type_info_TypeInfo'_account_address(s: $1_type_info_TypeInfo, x: int): $1_type_info_TypeInfo {
    $1_type_info_TypeInfo(x, s->$module_name, s->$struct_name)
}
function {:inline} $Update'$1_type_info_TypeInfo'_module_name(s: $1_type_info_TypeInfo, x: Vec (int)): $1_type_info_TypeInfo {
    $1_type_info_TypeInfo(s->$account_address, x, s->$struct_name)
}
function {:inline} $Update'$1_type_info_TypeInfo'_struct_name(s: $1_type_info_TypeInfo, x: Vec (int)): $1_type_info_TypeInfo {
    $1_type_info_TypeInfo(s->$account_address, s->$module_name, x)
}
function $IsValid'$1_type_info_TypeInfo'(s: $1_type_info_TypeInfo): bool {
    $IsValid'address'(s->$account_address)
      && $IsValid'vec'u8''(s->$module_name)
      && $IsValid'vec'u8''(s->$struct_name)
}
function {:inline} $IsEqual'$1_type_info_TypeInfo'(s1: $1_type_info_TypeInfo, s2: $1_type_info_TypeInfo): bool {
    $IsEqual'address'(s1->$account_address, s2->$account_address)
    && $IsEqual'vec'u8''(s1->$module_name, s2->$module_name)
    && $IsEqual'vec'u8''(s1->$struct_name, s2->$struct_name)}

// struct guid::GUID at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\sources\guid.move:7:5+50
datatype $1_guid_GUID {
    $1_guid_GUID($id: $1_guid_ID)
}
function {:inline} $Update'$1_guid_GUID'_id(s: $1_guid_GUID, x: $1_guid_ID): $1_guid_GUID {
    $1_guid_GUID(x)
}
function $IsValid'$1_guid_GUID'(s: $1_guid_GUID): bool {
    $IsValid'$1_guid_ID'(s->$id)
}
function {:inline} $IsEqual'$1_guid_GUID'(s1: $1_guid_GUID, s2: $1_guid_GUID): bool {
    s1 == s2
}

// struct guid::ID at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\sources\guid.move:12:5+209
datatype $1_guid_ID {
    $1_guid_ID($creation_num: int, $addr: int)
}
function {:inline} $Update'$1_guid_ID'_creation_num(s: $1_guid_ID, x: int): $1_guid_ID {
    $1_guid_ID(x, s->$addr)
}
function {:inline} $Update'$1_guid_ID'_addr(s: $1_guid_ID, x: int): $1_guid_ID {
    $1_guid_ID(s->$creation_num, x)
}
function $IsValid'$1_guid_ID'(s: $1_guid_ID): bool {
    $IsValid'u64'(s->$creation_num)
      && $IsValid'address'(s->$addr)
}
function {:inline} $IsEqual'$1_guid_ID'(s1: $1_guid_ID, s2: $1_guid_ID): bool {
    s1 == s2
}

// fun guid::create [baseline] at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\sources\guid.move:23:5+286
procedure {:inline 1} $1_guid_create(_$t0: int, _$t1: $Mutation (int)) returns ($ret0: $1_guid_GUID, $ret1: $Mutation (int))
{
    // declare local variables
    var $t2: int;
    var $t3: int;
    var $t4: int;
    var $t5: int;
    var $t6: int;
    var $t7: $1_guid_ID;
    var $t8: $1_guid_GUID;
    var $t0: int;
    var $t1: $Mutation (int);
    var $temp_0'$1_guid_GUID': $1_guid_GUID;
    var $temp_0'address': int;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // trace_local[addr]($t0) at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\sources\guid.move:23:5+1
    assume {:print "$at(129,836,837)"} true;
    assume {:print "$track_local(13,0,0):", $t0} $t0 == $t0;

    // trace_local[creation_num_ref]($t1) at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\sources\guid.move:23:5+1
    $temp_0'u64' := $Dereference($t1);
    assume {:print "$track_local(13,0,1):", $temp_0'u64'} $temp_0'u64' == $temp_0'u64';

    // $t3 := read_ref($t1) at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\sources\guid.move:24:28+17
    assume {:print "$at(129,940,957)"} true;
    $t3 := $Dereference($t1);

    // trace_local[creation_num]($t3) at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\sources\guid.move:24:13+12
    assume {:print "$track_local(13,0,2):", $t3} $t3 == $t3;

    // $t4 := 1 at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\sources\guid.move:25:44+1
    assume {:print "$at(129,1002,1003)"} true;
    $t4 := 1;
    assume $IsValid'u64'($t4);

    // $t5 := +($t3, $t4) on_abort goto L2 with $t6 at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\sources\guid.move:25:42+1
    call $t5 := $AddU64($t3, $t4);
    if ($abort_flag) {
        assume {:print "$at(129,1000,1001)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(13,0):", $t6} $t6 == $t6;
        goto L2;
    }

    // write_ref($t1, $t5) at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\sources\guid.move:25:9+36
    $t1 := $UpdateMutation($t1, $t5);

    // $t7 := pack guid::ID($t3, $t0) at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\sources\guid.move:27:17+70
    assume {:print "$at(129,1036,1106)"} true;
    $t7 := $1_guid_ID($t3, $t0);

    // $t8 := pack guid::GUID($t7) at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\sources\guid.move:26:9+103
    assume {:print "$at(129,1013,1116)"} true;
    $t8 := $1_guid_GUID($t7);

    // trace_return[0]($t8) at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\sources\guid.move:26:9+103
    assume {:print "$track_return(13,0,0):", $t8} $t8 == $t8;

    // trace_local[creation_num_ref]($t1) at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\sources\guid.move:26:9+103
    $temp_0'u64' := $Dereference($t1);
    assume {:print "$track_local(13,0,1):", $temp_0'u64'} $temp_0'u64' == $temp_0'u64';

    // label L1 at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\sources\guid.move:32:5+1
    assume {:print "$at(129,1121,1122)"} true;
L1:

    // return $t8 at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\sources\guid.move:32:5+1
    assume {:print "$at(129,1121,1122)"} true;
    $ret0 := $t8;
    $ret1 := $t1;
    return;

    // label L2 at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\sources\guid.move:32:5+1
L2:

    // abort($t6) at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\sources\guid.move:32:5+1
    assume {:print "$at(129,1121,1122)"} true;
    $abort_code := $t6;
    $abort_flag := true;
    return;

}

// spec fun at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'bool'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'bool'(bytes);
$IsValid'bool'($$res)));

// spec fun at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'u64'(bytes: Vec (int)): int;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'u64'(bytes);
$IsValid'u64'($$res)));

// spec fun at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'u256'(bytes: Vec (int)): int;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'u256'(bytes);
$IsValid'u256'($$res)));

// spec fun at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'address'(bytes: Vec (int)): int;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'address'(bytes);
$IsValid'address'($$res)));

// spec fun at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'signer'(bytes: Vec (int)): $signer;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'signer'(bytes);
$IsValid'signer'($$res)));

// spec fun at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'vec'u8''(bytes: Vec (int)): Vec (int);
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'vec'u8''(bytes);
$IsValid'vec'u8''($$res)));

// spec fun at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'vec'address''(bytes: Vec (int)): Vec (int);
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'vec'address''(bytes);
$IsValid'vec'address''($$res)));

// spec fun at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'vec'#0''(bytes: Vec (int)): Vec (#0);
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'vec'#0''(bytes);
$IsValid'vec'#0''($$res)));

// spec fun at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_option_Option'address''(bytes: Vec (int)): $1_option_Option'address';
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_option_Option'address''(bytes);
$IsValid'$1_option_Option'address''($$res)));

// spec fun at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_string_String'(bytes: Vec (int)): $1_string_String;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_string_String'(bytes);
$IsValid'$1_string_String'($$res)));

// spec fun at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_type_info_TypeInfo'(bytes: Vec (int)): $1_type_info_TypeInfo;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_type_info_TypeInfo'(bytes);
$IsValid'$1_type_info_TypeInfo'($$res)));

// spec fun at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_table_Table'u64_$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task''(bytes: Vec (int)): Table int ($747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task);
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_table_Table'u64_$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task''(bytes);
$IsValid'$1_table_Table'u64_$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task''($$res)));

// spec fun at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_guid_GUID'(bytes: Vec (int)): $1_guid_GUID;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_guid_GUID'(bytes);
$IsValid'$1_guid_GUID'($$res)));

// spec fun at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_guid_ID'(bytes: Vec (int)): $1_guid_ID;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_guid_ID'(bytes);
$IsValid'$1_guid_ID'($$res)));

// spec fun at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_event_EventHandle'$1_account_CoinRegisterEvent''(bytes: Vec (int)): $1_event_EventHandle'$1_account_CoinRegisterEvent';
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_event_EventHandle'$1_account_CoinRegisterEvent''(bytes);
$IsValid'$1_event_EventHandle'$1_account_CoinRegisterEvent''($$res)));

// spec fun at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_event_EventHandle'$1_account_KeyRotationEvent''(bytes: Vec (int)): $1_event_EventHandle'$1_account_KeyRotationEvent';
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_event_EventHandle'$1_account_KeyRotationEvent''(bytes);
$IsValid'$1_event_EventHandle'$1_account_KeyRotationEvent''($$res)));

// spec fun at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_event_EventHandle'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task''(bytes: Vec (int)): $1_event_EventHandle'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task';
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_event_EventHandle'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task''(bytes);
$IsValid'$1_event_EventHandle'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task''($$res)));

// spec fun at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_account_Account'(bytes: Vec (int)): $1_account_Account;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_account_Account'(bytes);
$IsValid'$1_account_Account'($$res)));

// spec fun at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_account_CapabilityOffer'$1_account_RotationCapability''(bytes: Vec (int)): $1_account_CapabilityOffer'$1_account_RotationCapability';
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_account_CapabilityOffer'$1_account_RotationCapability''(bytes);
$IsValid'$1_account_CapabilityOffer'$1_account_RotationCapability''($$res)));

// spec fun at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$1_account_CapabilityOffer'$1_account_SignerCapability''(bytes: Vec (int)): $1_account_CapabilityOffer'$1_account_SignerCapability';
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$1_account_CapabilityOffer'$1_account_SignerCapability''(bytes);
$IsValid'$1_account_CapabilityOffer'$1_account_SignerCapability''($$res)));

// spec fun at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task'(bytes: Vec (int)): $747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task'(bytes);
$IsValid'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task'($$res)));

// spec fun at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList'(bytes: Vec (int)): $747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList'(bytes);
$IsValid'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList'($$res)));

// spec fun at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:7:9+41
function  $1_from_bcs_deserialize'#0'(bytes: Vec (int)): #0;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserialize'#0'(bytes);
$IsValid'#0'($$res)));

// spec fun at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'bool'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'bool'(bytes);
$IsValid'bool'($$res)));

// spec fun at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'u64'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'u64'(bytes);
$IsValid'bool'($$res)));

// spec fun at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'u256'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'u256'(bytes);
$IsValid'bool'($$res)));

// spec fun at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'address'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'address'(bytes);
$IsValid'bool'($$res)));

// spec fun at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'signer'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'signer'(bytes);
$IsValid'bool'($$res)));

// spec fun at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'vec'u8''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'vec'u8''(bytes);
$IsValid'bool'($$res)));

// spec fun at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'vec'address''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'vec'address''(bytes);
$IsValid'bool'($$res)));

// spec fun at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'vec'#0''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'vec'#0''(bytes);
$IsValid'bool'($$res)));

// spec fun at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_option_Option'address''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_option_Option'address''(bytes);
$IsValid'bool'($$res)));

// spec fun at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_string_String'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_string_String'(bytes);
$IsValid'bool'($$res)));

// spec fun at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_type_info_TypeInfo'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_type_info_TypeInfo'(bytes);
$IsValid'bool'($$res)));

// spec fun at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_table_Table'u64_$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_table_Table'u64_$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task''(bytes);
$IsValid'bool'($$res)));

// spec fun at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_guid_GUID'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_guid_GUID'(bytes);
$IsValid'bool'($$res)));

// spec fun at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_guid_ID'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_guid_ID'(bytes);
$IsValid'bool'($$res)));

// spec fun at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_event_EventHandle'$1_account_CoinRegisterEvent''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_event_EventHandle'$1_account_CoinRegisterEvent''(bytes);
$IsValid'bool'($$res)));

// spec fun at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_event_EventHandle'$1_account_KeyRotationEvent''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_event_EventHandle'$1_account_KeyRotationEvent''(bytes);
$IsValid'bool'($$res)));

// spec fun at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_event_EventHandle'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_event_EventHandle'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task''(bytes);
$IsValid'bool'($$res)));

// spec fun at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_account_Account'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_account_Account'(bytes);
$IsValid'bool'($$res)));

// spec fun at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_account_CapabilityOffer'$1_account_RotationCapability''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_account_CapabilityOffer'$1_account_RotationCapability''(bytes);
$IsValid'bool'($$res)));

// spec fun at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$1_account_CapabilityOffer'$1_account_SignerCapability''(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$1_account_CapabilityOffer'$1_account_SignerCapability''(bytes);
$IsValid'bool'($$res)));

// spec fun at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task'(bytes);
$IsValid'bool'($$res)));

// spec fun at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList'(bytes);
$IsValid'bool'($$res)));

// spec fun at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\from_bcs.spec.move:11:9+47
function  $1_from_bcs_deserializable'#0'(bytes: Vec (int)): bool;
axiom (forall bytes: Vec (int) ::
(var $$res := $1_from_bcs_deserializable'#0'(bytes);
$IsValid'bool'($$res)));

// struct event::EventHandle<account::CoinRegisterEvent> at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\sources\event.move:34:5+224
datatype $1_event_EventHandle'$1_account_CoinRegisterEvent' {
    $1_event_EventHandle'$1_account_CoinRegisterEvent'($counter: int, $guid: $1_guid_GUID)
}
function {:inline} $Update'$1_event_EventHandle'$1_account_CoinRegisterEvent''_counter(s: $1_event_EventHandle'$1_account_CoinRegisterEvent', x: int): $1_event_EventHandle'$1_account_CoinRegisterEvent' {
    $1_event_EventHandle'$1_account_CoinRegisterEvent'(x, s->$guid)
}
function {:inline} $Update'$1_event_EventHandle'$1_account_CoinRegisterEvent''_guid(s: $1_event_EventHandle'$1_account_CoinRegisterEvent', x: $1_guid_GUID): $1_event_EventHandle'$1_account_CoinRegisterEvent' {
    $1_event_EventHandle'$1_account_CoinRegisterEvent'(s->$counter, x)
}
function $IsValid'$1_event_EventHandle'$1_account_CoinRegisterEvent''(s: $1_event_EventHandle'$1_account_CoinRegisterEvent'): bool {
    $IsValid'u64'(s->$counter)
      && $IsValid'$1_guid_GUID'(s->$guid)
}
function {:inline} $IsEqual'$1_event_EventHandle'$1_account_CoinRegisterEvent''(s1: $1_event_EventHandle'$1_account_CoinRegisterEvent', s2: $1_event_EventHandle'$1_account_CoinRegisterEvent'): bool {
    s1 == s2
}

// struct event::EventHandle<account::KeyRotationEvent> at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\sources\event.move:34:5+224
datatype $1_event_EventHandle'$1_account_KeyRotationEvent' {
    $1_event_EventHandle'$1_account_KeyRotationEvent'($counter: int, $guid: $1_guid_GUID)
}
function {:inline} $Update'$1_event_EventHandle'$1_account_KeyRotationEvent''_counter(s: $1_event_EventHandle'$1_account_KeyRotationEvent', x: int): $1_event_EventHandle'$1_account_KeyRotationEvent' {
    $1_event_EventHandle'$1_account_KeyRotationEvent'(x, s->$guid)
}
function {:inline} $Update'$1_event_EventHandle'$1_account_KeyRotationEvent''_guid(s: $1_event_EventHandle'$1_account_KeyRotationEvent', x: $1_guid_GUID): $1_event_EventHandle'$1_account_KeyRotationEvent' {
    $1_event_EventHandle'$1_account_KeyRotationEvent'(s->$counter, x)
}
function $IsValid'$1_event_EventHandle'$1_account_KeyRotationEvent''(s: $1_event_EventHandle'$1_account_KeyRotationEvent'): bool {
    $IsValid'u64'(s->$counter)
      && $IsValid'$1_guid_GUID'(s->$guid)
}
function {:inline} $IsEqual'$1_event_EventHandle'$1_account_KeyRotationEvent''(s1: $1_event_EventHandle'$1_account_KeyRotationEvent', s2: $1_event_EventHandle'$1_account_KeyRotationEvent'): bool {
    s1 == s2
}

// struct event::EventHandle<todolist::Task> at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\sources\event.move:34:5+224
datatype $1_event_EventHandle'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task' {
    $1_event_EventHandle'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task'($counter: int, $guid: $1_guid_GUID)
}
function {:inline} $Update'$1_event_EventHandle'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task''_counter(s: $1_event_EventHandle'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task', x: int): $1_event_EventHandle'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task' {
    $1_event_EventHandle'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task'(x, s->$guid)
}
function {:inline} $Update'$1_event_EventHandle'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task''_guid(s: $1_event_EventHandle'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task', x: $1_guid_GUID): $1_event_EventHandle'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task' {
    $1_event_EventHandle'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task'(s->$counter, x)
}
function $IsValid'$1_event_EventHandle'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task''(s: $1_event_EventHandle'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task'): bool {
    $IsValid'u64'(s->$counter)
      && $IsValid'$1_guid_GUID'(s->$guid)
}
function {:inline} $IsEqual'$1_event_EventHandle'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task''(s1: $1_event_EventHandle'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task', s2: $1_event_EventHandle'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task'): bool {
    s1 == s2
}

// fun event::new_event_handle<todolist::Task> [baseline] at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\sources\event.move:43:5+165
procedure {:inline 1} $1_event_new_event_handle'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task'(_$t0: $1_guid_GUID) returns ($ret0: $1_event_EventHandle'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task')
{
    // declare local variables
    var $t1: int;
    var $t2: $1_event_EventHandle'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task';
    var $t0: $1_guid_GUID;
    var $temp_0'$1_event_EventHandle'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task'': $1_event_EventHandle'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task';
    var $temp_0'$1_guid_GUID': $1_guid_GUID;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[guid]($t0) at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\sources\event.move:43:5+1
    assume {:print "$at(121,1543,1544)"} true;
    assume {:print "$track_local(15,5,0):", $t0} $t0 == $t0;

    // $t1 := 0 at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\sources\event.move:45:22+1
    assume {:print "$at(121,1672,1673)"} true;
    $t1 := 0;
    assume $IsValid'u64'($t1);

    // $t2 := pack event::EventHandle<#0>($t1, $t0) at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\sources\event.move:44:9+68
    assume {:print "$at(121,1634,1702)"} true;
    $t2 := $1_event_EventHandle'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task'($t1, $t0);

    // trace_return[0]($t2) at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\sources\event.move:44:9+68
    assume {:print "$track_return(15,5,0):", $t2} $t2 == $t2;

    // label L1 at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\sources\event.move:48:5+1
    assume {:print "$at(121,1707,1708)"} true;
L1:

    // return $t2 at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\sources\event.move:48:5+1
    assume {:print "$at(121,1707,1708)"} true;
    $ret0 := $t2;
    return;

}

// struct account::Account at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\sources\account.move:34:5+401
datatype $1_account_Account {
    $1_account_Account($authentication_key: Vec (int), $sequence_number: int, $guid_creation_num: int, $coin_register_events: $1_event_EventHandle'$1_account_CoinRegisterEvent', $key_rotation_events: $1_event_EventHandle'$1_account_KeyRotationEvent', $rotation_capability_offer: $1_account_CapabilityOffer'$1_account_RotationCapability', $signer_capability_offer: $1_account_CapabilityOffer'$1_account_SignerCapability')
}
function {:inline} $Update'$1_account_Account'_authentication_key(s: $1_account_Account, x: Vec (int)): $1_account_Account {
    $1_account_Account(x, s->$sequence_number, s->$guid_creation_num, s->$coin_register_events, s->$key_rotation_events, s->$rotation_capability_offer, s->$signer_capability_offer)
}
function {:inline} $Update'$1_account_Account'_sequence_number(s: $1_account_Account, x: int): $1_account_Account {
    $1_account_Account(s->$authentication_key, x, s->$guid_creation_num, s->$coin_register_events, s->$key_rotation_events, s->$rotation_capability_offer, s->$signer_capability_offer)
}
function {:inline} $Update'$1_account_Account'_guid_creation_num(s: $1_account_Account, x: int): $1_account_Account {
    $1_account_Account(s->$authentication_key, s->$sequence_number, x, s->$coin_register_events, s->$key_rotation_events, s->$rotation_capability_offer, s->$signer_capability_offer)
}
function {:inline} $Update'$1_account_Account'_coin_register_events(s: $1_account_Account, x: $1_event_EventHandle'$1_account_CoinRegisterEvent'): $1_account_Account {
    $1_account_Account(s->$authentication_key, s->$sequence_number, s->$guid_creation_num, x, s->$key_rotation_events, s->$rotation_capability_offer, s->$signer_capability_offer)
}
function {:inline} $Update'$1_account_Account'_key_rotation_events(s: $1_account_Account, x: $1_event_EventHandle'$1_account_KeyRotationEvent'): $1_account_Account {
    $1_account_Account(s->$authentication_key, s->$sequence_number, s->$guid_creation_num, s->$coin_register_events, x, s->$rotation_capability_offer, s->$signer_capability_offer)
}
function {:inline} $Update'$1_account_Account'_rotation_capability_offer(s: $1_account_Account, x: $1_account_CapabilityOffer'$1_account_RotationCapability'): $1_account_Account {
    $1_account_Account(s->$authentication_key, s->$sequence_number, s->$guid_creation_num, s->$coin_register_events, s->$key_rotation_events, x, s->$signer_capability_offer)
}
function {:inline} $Update'$1_account_Account'_signer_capability_offer(s: $1_account_Account, x: $1_account_CapabilityOffer'$1_account_SignerCapability'): $1_account_Account {
    $1_account_Account(s->$authentication_key, s->$sequence_number, s->$guid_creation_num, s->$coin_register_events, s->$key_rotation_events, s->$rotation_capability_offer, x)
}
function $IsValid'$1_account_Account'(s: $1_account_Account): bool {
    $IsValid'vec'u8''(s->$authentication_key)
      && $IsValid'u64'(s->$sequence_number)
      && $IsValid'u64'(s->$guid_creation_num)
      && $IsValid'$1_event_EventHandle'$1_account_CoinRegisterEvent''(s->$coin_register_events)
      && $IsValid'$1_event_EventHandle'$1_account_KeyRotationEvent''(s->$key_rotation_events)
      && $IsValid'$1_account_CapabilityOffer'$1_account_RotationCapability''(s->$rotation_capability_offer)
      && $IsValid'$1_account_CapabilityOffer'$1_account_SignerCapability''(s->$signer_capability_offer)
}
function {:inline} $IsEqual'$1_account_Account'(s1: $1_account_Account, s2: $1_account_Account): bool {
    $IsEqual'vec'u8''(s1->$authentication_key, s2->$authentication_key)
    && $IsEqual'u64'(s1->$sequence_number, s2->$sequence_number)
    && $IsEqual'u64'(s1->$guid_creation_num, s2->$guid_creation_num)
    && $IsEqual'$1_event_EventHandle'$1_account_CoinRegisterEvent''(s1->$coin_register_events, s2->$coin_register_events)
    && $IsEqual'$1_event_EventHandle'$1_account_KeyRotationEvent''(s1->$key_rotation_events, s2->$key_rotation_events)
    && $IsEqual'$1_account_CapabilityOffer'$1_account_RotationCapability''(s1->$rotation_capability_offer, s2->$rotation_capability_offer)
    && $IsEqual'$1_account_CapabilityOffer'$1_account_SignerCapability''(s1->$signer_capability_offer, s2->$signer_capability_offer)}
var $1_account_Account_$memory: $Memory $1_account_Account;

// struct account::CapabilityOffer<account::RotationCapability> at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\sources\account.move:53:5+68
datatype $1_account_CapabilityOffer'$1_account_RotationCapability' {
    $1_account_CapabilityOffer'$1_account_RotationCapability'($for: $1_option_Option'address')
}
function {:inline} $Update'$1_account_CapabilityOffer'$1_account_RotationCapability''_for(s: $1_account_CapabilityOffer'$1_account_RotationCapability', x: $1_option_Option'address'): $1_account_CapabilityOffer'$1_account_RotationCapability' {
    $1_account_CapabilityOffer'$1_account_RotationCapability'(x)
}
function $IsValid'$1_account_CapabilityOffer'$1_account_RotationCapability''(s: $1_account_CapabilityOffer'$1_account_RotationCapability'): bool {
    $IsValid'$1_option_Option'address''(s->$for)
}
function {:inline} $IsEqual'$1_account_CapabilityOffer'$1_account_RotationCapability''(s1: $1_account_CapabilityOffer'$1_account_RotationCapability', s2: $1_account_CapabilityOffer'$1_account_RotationCapability'): bool {
    $IsEqual'$1_option_Option'address''(s1->$for, s2->$for)}

// struct account::CapabilityOffer<account::SignerCapability> at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\sources\account.move:53:5+68
datatype $1_account_CapabilityOffer'$1_account_SignerCapability' {
    $1_account_CapabilityOffer'$1_account_SignerCapability'($for: $1_option_Option'address')
}
function {:inline} $Update'$1_account_CapabilityOffer'$1_account_SignerCapability''_for(s: $1_account_CapabilityOffer'$1_account_SignerCapability', x: $1_option_Option'address'): $1_account_CapabilityOffer'$1_account_SignerCapability' {
    $1_account_CapabilityOffer'$1_account_SignerCapability'(x)
}
function $IsValid'$1_account_CapabilityOffer'$1_account_SignerCapability''(s: $1_account_CapabilityOffer'$1_account_SignerCapability'): bool {
    $IsValid'$1_option_Option'address''(s->$for)
}
function {:inline} $IsEqual'$1_account_CapabilityOffer'$1_account_SignerCapability''(s1: $1_account_CapabilityOffer'$1_account_SignerCapability', s2: $1_account_CapabilityOffer'$1_account_SignerCapability'): bool {
    $IsEqual'$1_option_Option'address''(s1->$for, s2->$for)}

// struct account::CoinRegisterEvent at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\sources\account.move:49:5+77
datatype $1_account_CoinRegisterEvent {
    $1_account_CoinRegisterEvent($type_info: $1_type_info_TypeInfo)
}
function {:inline} $Update'$1_account_CoinRegisterEvent'_type_info(s: $1_account_CoinRegisterEvent, x: $1_type_info_TypeInfo): $1_account_CoinRegisterEvent {
    $1_account_CoinRegisterEvent(x)
}
function $IsValid'$1_account_CoinRegisterEvent'(s: $1_account_CoinRegisterEvent): bool {
    $IsValid'$1_type_info_TypeInfo'(s->$type_info)
}
function {:inline} $IsEqual'$1_account_CoinRegisterEvent'(s1: $1_account_CoinRegisterEvent, s2: $1_account_CoinRegisterEvent): bool {
    $IsEqual'$1_type_info_TypeInfo'(s1->$type_info, s2->$type_info)}

// struct account::KeyRotationEvent at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\sources\account.move:44:5+135
datatype $1_account_KeyRotationEvent {
    $1_account_KeyRotationEvent($old_authentication_key: Vec (int), $new_authentication_key: Vec (int))
}
function {:inline} $Update'$1_account_KeyRotationEvent'_old_authentication_key(s: $1_account_KeyRotationEvent, x: Vec (int)): $1_account_KeyRotationEvent {
    $1_account_KeyRotationEvent(x, s->$new_authentication_key)
}
function {:inline} $Update'$1_account_KeyRotationEvent'_new_authentication_key(s: $1_account_KeyRotationEvent, x: Vec (int)): $1_account_KeyRotationEvent {
    $1_account_KeyRotationEvent(s->$old_authentication_key, x)
}
function $IsValid'$1_account_KeyRotationEvent'(s: $1_account_KeyRotationEvent): bool {
    $IsValid'vec'u8''(s->$old_authentication_key)
      && $IsValid'vec'u8''(s->$new_authentication_key)
}
function {:inline} $IsEqual'$1_account_KeyRotationEvent'(s1: $1_account_KeyRotationEvent, s2: $1_account_KeyRotationEvent): bool {
    $IsEqual'vec'u8''(s1->$old_authentication_key, s2->$old_authentication_key)
    && $IsEqual'vec'u8''(s1->$new_authentication_key, s2->$new_authentication_key)}

// struct account::RotationCapability at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\sources\account.move:55:5+62
datatype $1_account_RotationCapability {
    $1_account_RotationCapability($account: int)
}
function {:inline} $Update'$1_account_RotationCapability'_account(s: $1_account_RotationCapability, x: int): $1_account_RotationCapability {
    $1_account_RotationCapability(x)
}
function $IsValid'$1_account_RotationCapability'(s: $1_account_RotationCapability): bool {
    $IsValid'address'(s->$account)
}
function {:inline} $IsEqual'$1_account_RotationCapability'(s1: $1_account_RotationCapability, s2: $1_account_RotationCapability): bool {
    s1 == s2
}

// struct account::SignerCapability at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\sources\account.move:57:5+60
datatype $1_account_SignerCapability {
    $1_account_SignerCapability($account: int)
}
function {:inline} $Update'$1_account_SignerCapability'_account(s: $1_account_SignerCapability, x: int): $1_account_SignerCapability {
    $1_account_SignerCapability(x)
}
function $IsValid'$1_account_SignerCapability'(s: $1_account_SignerCapability): bool {
    $IsValid'address'(s->$account)
}
function {:inline} $IsEqual'$1_account_SignerCapability'(s1: $1_account_SignerCapability, s2: $1_account_SignerCapability): bool {
    s1 == s2
}

// fun account::new_event_handle<todolist::Task> [baseline] at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\sources\account.move:721:5+157
procedure {:inline 1} $1_account_new_event_handle'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task'(_$t0: $signer) returns ($ret0: $1_event_EventHandle'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task')
{
    // declare local variables
    var $t1: int;
    var $t2: $1_account_Account;
    var $t3: int;
    var $t4: int;
    var $t5: $1_account_Account;
    var $t6: $1_guid_GUID;
    var $t7: int;
    var $t8: $1_event_EventHandle'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task';
    var $t0: $signer;
    var $temp_0'$1_event_EventHandle'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task'': $1_event_EventHandle'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task';
    var $temp_0'signer': $signer;
    $t0 := _$t0;

    // bytecode translation starts here
    // assume Identical($t1, signer::$address_of($t0)) at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\sources\account.spec.move:638:9+39
    assume {:print "$at(82,31785,31824)"} true;
    assume ($t1 == $1_signer_$address_of($t0));

    // assume Identical($t2, global<account::Account>($t1)) at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\sources\account.spec.move:639:9+36
    assume {:print "$at(82,31833,31869)"} true;
    assume ($t2 == $ResourceValue($1_account_Account_$memory, $t1));

    // trace_local[account]($t0) at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\sources\account.move:721:5+1
    assume {:print "$at(81,40755,40756)"} true;
    assume {:print "$track_local(18,21,0):", $t0} $t0 == $t0;

    // assume Identical($t3, signer::$address_of($t0)) at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\sources\account.spec.move:622:9+46
    assume {:print "$at(82,31152,31198)"} true;
    assume ($t3 == $1_signer_$address_of($t0));

    // assume Identical($t4, signer::$address_of($t0)) at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\sources\account.spec.move:638:9+39
    assume {:print "$at(82,31785,31824)"} true;
    assume ($t4 == $1_signer_$address_of($t0));

    // assume Identical($t5, global<account::Account>($t4)) at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\sources\account.spec.move:639:9+36
    assume {:print "$at(82,31833,31869)"} true;
    assume ($t5 == $ResourceValue($1_account_Account_$memory, $t4));

    // $t6 := account::create_guid($t0) on_abort goto L2 with $t7 at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\sources\account.move:722:33+20
    assume {:print "$at(81,40885,40905)"} true;
    call $t6 := $1_account_create_guid($t0);
    if ($abort_flag) {
        assume {:print "$at(81,40885,40905)"} true;
        $t7 := $abort_code;
        assume {:print "$track_abort(18,21):", $t7} $t7 == $t7;
        goto L2;
    }

    // $t8 := event::new_event_handle<#0>($t6) on_abort goto L2 with $t7 at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\sources\account.move:722:9+45
    call $t8 := $1_event_new_event_handle'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task'($t6);
    if ($abort_flag) {
        assume {:print "$at(81,40861,40906)"} true;
        $t7 := $abort_code;
        assume {:print "$track_abort(18,21):", $t7} $t7 == $t7;
        goto L2;
    }

    // trace_return[0]($t8) at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\sources\account.move:722:9+45
    assume {:print "$track_return(18,21,0):", $t8} $t8 == $t8;

    // label L1 at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\sources\account.move:723:5+1
    assume {:print "$at(81,40911,40912)"} true;
L1:

    // return $t8 at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\sources\account.move:723:5+1
    assume {:print "$at(81,40911,40912)"} true;
    $ret0 := $t8;
    return;

    // label L2 at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\sources\account.move:723:5+1
L2:

    // abort($t7) at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\sources\account.move:723:5+1
    assume {:print "$at(81,40911,40912)"} true;
    $abort_code := $t7;
    $abort_flag := true;
    return;

}

// fun account::create_guid [baseline] at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\sources\account.move:706:5+436
procedure {:inline 1} $1_account_create_guid(_$t0: $signer) returns ($ret0: $1_guid_GUID)
{
    // declare local variables
    var $t1: $Mutation ($1_account_Account);
    var $t2: int;
    var $t3: $1_guid_GUID;
    var $t4: int;
    var $t5: int;
    var $t6: $1_account_Account;
    var $t7: int;
    var $t8: int;
    var $t9: $Mutation ($1_account_Account);
    var $t10: $Mutation (int);
    var $t11: $1_guid_GUID;
    var $t12: int;
    var $t13: int;
    var $t14: bool;
    var $t15: int;
    var $t16: int;
    var $t0: $signer;
    var $1_account_Account_$modifies: [int]bool;
    var $temp_0'$1_account_Account': $1_account_Account;
    var $temp_0'$1_guid_GUID': $1_guid_GUID;
    var $temp_0'address': int;
    var $temp_0'signer': $signer;
    $t0 := _$t0;

    // bytecode translation starts here
    // assume Identical($t4, signer::$address_of($t0)) at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\sources\account.spec.move:622:9+46
    assume {:print "$at(82,31152,31198)"} true;
    assume ($t4 == $1_signer_$address_of($t0));

    // assume Identical($t5, signer::$address_of($t0)) at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\sources\account.spec.move:638:9+39
    assume {:print "$at(82,31785,31824)"} true;
    assume ($t5 == $1_signer_$address_of($t0));

    // assume Identical($t6, global<account::Account>($t5)) at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\sources\account.spec.move:639:9+36
    assume {:print "$at(82,31833,31869)"} true;
    assume ($t6 == $ResourceValue($1_account_Account_$memory, $t5));

    // trace_local[account_signer]($t0) at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\sources\account.move:706:5+1
    assume {:print "$at(81,40119,40120)"} true;
    assume {:print "$track_local(18,6,0):", $t0} $t0 == $t0;

    // $t7 := signer::address_of($t0) on_abort goto L4 with $t8 at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\sources\account.move:707:20+34
    assume {:print "$at(81,40217,40251)"} true;
    call $t7 := $1_signer_address_of($t0);
    if ($abort_flag) {
        assume {:print "$at(81,40217,40251)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(18,6):", $t8} $t8 == $t8;
        goto L4;
    }

    // trace_local[addr]($t7) at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\sources\account.move:707:13+4
    assume {:print "$track_local(18,6,2):", $t7} $t7 == $t7;

    // $t9 := borrow_global<account::Account>($t7) on_abort goto L4 with $t8 at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\sources\account.move:708:23+17
    assume {:print "$at(81,40275,40292)"} true;
    if (!$ResourceExists($1_account_Account_$memory, $t7)) {
        call $ExecFailureAbort();
    } else {
        $t9 := $Mutation($Global($t7), EmptyVec(), $ResourceValue($1_account_Account_$memory, $t7));
    }
    if ($abort_flag) {
        assume {:print "$at(81,40275,40292)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(18,6):", $t8} $t8 == $t8;
        goto L4;
    }

    // trace_local[account]($t9) at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\sources\account.move:708:13+7
    $temp_0'$1_account_Account' := $Dereference($t9);
    assume {:print "$track_local(18,6,1):", $temp_0'$1_account_Account'} $temp_0'$1_account_Account' == $temp_0'$1_account_Account';

    // $t10 := borrow_field<account::Account>.guid_creation_num($t9) at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\sources\account.move:709:39+30
    assume {:print "$at(81,40347,40377)"} true;
    $t10 := $ChildMutation($t9, 2, $Dereference($t9)->$guid_creation_num);

    // $t11 := guid::create($t7, $t10) on_abort goto L4 with $t8 at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\sources\account.move:709:20+50
    call $t11,$t10 := $1_guid_create($t7, $t10);
    if ($abort_flag) {
        assume {:print "$at(81,40328,40378)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(18,6):", $t8} $t8 == $t8;
        goto L4;
    }

    // write_back[Reference($t9).guid_creation_num (u64)]($t10) at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\sources\account.move:709:20+50
    $t9 := $UpdateMutation($t9, $Update'$1_account_Account'_guid_creation_num($Dereference($t9), $Dereference($t10)));

    // trace_local[guid]($t11) at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\sources\account.move:709:13+4
    assume {:print "$track_local(18,6,3):", $t11} $t11 == $t11;

    // $t12 := get_field<account::Account>.guid_creation_num($t9) at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\sources\account.move:711:13+25
    assume {:print "$at(81,40409,40434)"} true;
    $t12 := $Dereference($t9)->$guid_creation_num;

    // pack_ref_deep($t9) at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\sources\account.move:711:13+25

    // write_back[account::Account@]($t9) at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\sources\account.move:711:13+25
    $1_account_Account_$memory := $ResourceUpdate($1_account_Account_$memory, $GlobalLocationAddress($t9),
        $Dereference($t9));

    // $t13 := 1125899906842624 at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\sources\account.move:711:41+21
    $t13 := 1125899906842624;
    assume $IsValid'u64'($t13);

    // $t14 := <($t12, $t13) at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\sources\account.move:711:39+1
    call $t14 := $Lt($t12, $t13);

    // if ($t14) goto L1 else goto L0 at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\sources\account.move:710:9+147
    assume {:print "$at(81,40388,40535)"} true;
    if ($t14) { goto L1; } else { goto L0; }

    // label L1 at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\sources\account.move:710:9+147
L1:

    // goto L2 at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\sources\account.move:710:9+147
    assume {:print "$at(81,40388,40535)"} true;
    goto L2;

    // label L0 at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\sources\account.move:712:33+31
    assume {:print "$at(81,40492,40523)"} true;
L0:

    // $t15 := 20 at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\sources\account.move:712:33+31
    assume {:print "$at(81,40492,40523)"} true;
    $t15 := 20;
    assume $IsValid'u64'($t15);

    // $t16 := error::out_of_range($t15) on_abort goto L4 with $t8 at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\sources\account.move:712:13+52
    call $t16 := $1_error_out_of_range($t15);
    if ($abort_flag) {
        assume {:print "$at(81,40472,40524)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(18,6):", $t8} $t8 == $t8;
        goto L4;
    }

    // trace_abort($t16) at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\sources\account.move:710:9+147
    assume {:print "$at(81,40388,40535)"} true;
    assume {:print "$track_abort(18,6):", $t16} $t16 == $t16;

    // $t8 := move($t16) at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\sources\account.move:710:9+147
    $t8 := $t16;

    // goto L4 at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\sources\account.move:710:9+147
    goto L4;

    // label L2 at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\sources\account.move:714:9+4
    assume {:print "$at(81,40545,40549)"} true;
L2:

    // trace_return[0]($t11) at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\sources\account.move:714:9+4
    assume {:print "$at(81,40545,40549)"} true;
    assume {:print "$track_return(18,6,0):", $t11} $t11 == $t11;

    // label L3 at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\sources\account.move:715:5+1
    assume {:print "$at(81,40554,40555)"} true;
L3:

    // return $t11 at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\sources\account.move:715:5+1
    assume {:print "$at(81,40554,40555)"} true;
    $ret0 := $t11;
    return;

    // label L4 at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\sources\account.move:715:5+1
L4:

    // abort($t8) at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\sources\account.move:715:5+1
    assume {:print "$at(81,40554,40555)"} true;
    $abort_code := $t8;
    $abort_flag := true;
    return;

}

// spec fun at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\hash.spec.move:7:9+50
function  $1_aptos_hash_spec_keccak256(bytes: Vec (int)): Vec (int);
axiom (forall bytes: Vec (int) ::
(var $$res := $1_aptos_hash_spec_keccak256(bytes);
$IsValid'vec'u8''($$res)));

// spec fun at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\hash.spec.move:12:9+58
function  $1_aptos_hash_spec_sha2_512_internal(bytes: Vec (int)): Vec (int);
axiom (forall bytes: Vec (int) ::
(var $$res := $1_aptos_hash_spec_sha2_512_internal(bytes);
$IsValid'vec'u8''($$res)));

// spec fun at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\hash.spec.move:17:9+58
function  $1_aptos_hash_spec_sha3_512_internal(bytes: Vec (int)): Vec (int);
axiom (forall bytes: Vec (int) ::
(var $$res := $1_aptos_hash_spec_sha3_512_internal(bytes);
$IsValid'vec'u8''($$res)));

// spec fun at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\hash.spec.move:22:9+59
function  $1_aptos_hash_spec_ripemd160_internal(bytes: Vec (int)): Vec (int);
axiom (forall bytes: Vec (int) ::
(var $$res := $1_aptos_hash_spec_ripemd160_internal(bytes);
$IsValid'vec'u8''($$res)));

// spec fun at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\../aptos-stdlib\sources\hash.spec.move:27:9+61
function  $1_aptos_hash_spec_blake2b_256_internal(bytes: Vec (int)): Vec (int);
axiom (forall bytes: Vec (int) ::
(var $$res := $1_aptos_hash_spec_blake2b_256_internal(bytes);
$IsValid'vec'u8''($$res)));

// struct todolist::Task at E:\todo-with-aptos\sources\todolist.move:19:5+143
datatype $747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task {
    $747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task($task_id: int, $address: int, $content: $1_string_String, $completed: bool)
}
function {:inline} $Update'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task'_task_id(s: $747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task, x: int): $747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task {
    $747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task(x, s->$address, s->$content, s->$completed)
}
function {:inline} $Update'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task'_address(s: $747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task, x: int): $747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task {
    $747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task(s->$task_id, x, s->$content, s->$completed)
}
function {:inline} $Update'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task'_content(s: $747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task, x: $1_string_String): $747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task {
    $747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task(s->$task_id, s->$address, x, s->$completed)
}
function {:inline} $Update'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task'_completed(s: $747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task, x: bool): $747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task {
    $747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task(s->$task_id, s->$address, s->$content, x)
}
function $IsValid'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task'(s: $747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task): bool {
    $IsValid'u64'(s->$task_id)
      && $IsValid'address'(s->$address)
      && $IsValid'$1_string_String'(s->$content)
      && $IsValid'bool'(s->$completed)
}
function {:inline} $IsEqual'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task'(s1: $747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task, s2: $747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task): bool {
    $IsEqual'u64'(s1->$task_id, s2->$task_id)
    && $IsEqual'address'(s1->$address, s2->$address)
    && $IsEqual'$1_string_String'(s1->$content, s2->$content)
    && $IsEqual'bool'(s1->$completed, s2->$completed)}

// struct todolist::TodoList at E:\todo-with-aptos\sources\todolist.move:13:5+144
datatype $747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList {
    $747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList($tasks: Table int ($747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task), $set_task_event: $1_event_EventHandle'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task', $task_counter: int)
}
function {:inline} $Update'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList'_tasks(s: $747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList, x: Table int ($747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task)): $747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList {
    $747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList(x, s->$set_task_event, s->$task_counter)
}
function {:inline} $Update'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList'_set_task_event(s: $747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList, x: $1_event_EventHandle'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task'): $747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList {
    $747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList(s->$tasks, x, s->$task_counter)
}
function {:inline} $Update'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList'_task_counter(s: $747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList, x: int): $747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList {
    $747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList(s->$tasks, s->$set_task_event, x)
}
function $IsValid'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList'(s: $747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList): bool {
    $IsValid'$1_table_Table'u64_$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task''(s->$tasks)
      && $IsValid'$1_event_EventHandle'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task''(s->$set_task_event)
      && $IsValid'u64'(s->$task_counter)
}
function {:inline} $IsEqual'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList'(s1: $747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList, s2: $747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList): bool {
    s1 == s2
}
var $747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList_$memory: $Memory $747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList;

// fun todolist::complete_task [verification] at E:\todo-with-aptos\sources\todolist.move:52:5+562
procedure {:timeLimit 40} $747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_complete_task$verify(_$t0: $signer, _$t1: int) returns ()
{
    // declare local variables
    var $t2: int;
    var $t3: $Mutation ($747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task);
    var $t4: $Mutation ($747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList);
    var $t5: int;
    var $t6: int;
    var $t7: bool;
    var $t8: int;
    var $t9: $Mutation ($747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList);
    var $t10: Table int ($747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task);
    var $t11: bool;
    var $t12: int;
    var $t13: $Mutation (Table int ($747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task));
    var $t14: $Mutation ($747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task);
    var $t15: bool;
    var $t16: bool;
    var $t17: bool;
    var $t18: int;
    var $t19: bool;
    var $t20: $Mutation (bool);
    var $t0: $signer;
    var $t1: int;
    var $temp_0'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task': $747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task;
    var $temp_0'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList': $747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList;
    var $temp_0'address': int;
    var $temp_0'signer': $signer;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at E:\todo-with-aptos\sources\todolist.move:52:5+1
    assume {:print "$at(2,1740,1741)"} true;
    assume $IsValid'signer'($t0) && $1_signer_is_txn_signer($t0) && $1_signer_is_txn_signer_addr($t0->$addr);

    // assume WellFormed($t1) at E:\todo-with-aptos\sources\todolist.move:52:5+1
    assume $IsValid'u64'($t1);

    // assume forall $rsc: todolist::TodoList: ResourceDomain<todolist::TodoList>(): WellFormed($rsc) at E:\todo-with-aptos\sources\todolist.move:52:5+1
    assume (forall $a_0: int :: {$ResourceValue($747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList_$memory, $a_0)}(var $rsc := $ResourceValue($747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList_$memory, $a_0);
    ($IsValid'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList'($rsc))));

    // trace_local[account]($t0) at E:\todo-with-aptos\sources\todolist.move:52:5+1
    assume {:print "$track_local(67,0,0):", $t0} $t0 == $t0;

    // trace_local[task_id]($t1) at E:\todo-with-aptos\sources\todolist.move:52:5+1
    assume {:print "$track_local(67,0,1):", $t1} $t1 == $t1;

    // $t5 := signer::address_of($t0) on_abort goto L10 with $t6 at E:\todo-with-aptos\sources\todolist.move:53:30+27
    assume {:print "$at(2,1853,1880)"} true;
    call $t5 := $1_signer_address_of($t0);
    if ($abort_flag) {
        assume {:print "$at(2,1853,1880)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(67,0):", $t6} $t6 == $t6;
        goto L10;
    }

    // trace_local[signer_address]($t5) at E:\todo-with-aptos\sources\todolist.move:53:13+14
    assume {:print "$track_local(67,0,2):", $t5} $t5 == $t5;

    // $t7 := exists<todolist::TodoList>($t5) at E:\todo-with-aptos\sources\todolist.move:54:17+6
    assume {:print "$at(2,1899,1905)"} true;
    $t7 := $ResourceExists($747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList_$memory, $t5);

    // if ($t7) goto L1 else goto L0 at E:\todo-with-aptos\sources\todolist.move:54:9+60
    if ($t7) { goto L1; } else { goto L0; }

    // label L1 at E:\todo-with-aptos\sources\todolist.move:54:9+60
L1:

    // goto L2 at E:\todo-with-aptos\sources\todolist.move:54:9+60
    assume {:print "$at(2,1891,1951)"} true;
    goto L2;

    // label L0 at E:\todo-with-aptos\sources\todolist.move:54:51+17
L0:

    // $t8 := 1 at E:\todo-with-aptos\sources\todolist.move:54:51+17
    assume {:print "$at(2,1933,1950)"} true;
    $t8 := 1;
    assume $IsValid'u64'($t8);

    // trace_abort($t8) at E:\todo-with-aptos\sources\todolist.move:54:9+60
    assume {:print "$at(2,1891,1951)"} true;
    assume {:print "$track_abort(67,0):", $t8} $t8 == $t8;

    // $t6 := move($t8) at E:\todo-with-aptos\sources\todolist.move:54:9+60
    $t6 := $t8;

    // goto L10 at E:\todo-with-aptos\sources\todolist.move:54:9+60
    goto L10;

    // label L2 at E:\todo-with-aptos\sources\todolist.move:55:53+14
    assume {:print "$at(2,2006,2020)"} true;
L2:

    // $t9 := borrow_global<todolist::TodoList>($t5) on_abort goto L10 with $t6 at E:\todo-with-aptos\sources\todolist.move:55:25+17
    assume {:print "$at(2,1978,1995)"} true;
    if (!$ResourceExists($747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList_$memory, $t5)) {
        call $ExecFailureAbort();
    } else {
        $t9 := $Mutation($Global($t5), EmptyVec(), $ResourceValue($747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList_$memory, $t5));
    }
    if ($abort_flag) {
        assume {:print "$at(2,1978,1995)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(67,0):", $t6} $t6 == $t6;
        goto L10;
    }

    // trace_local[todo_list]($t9) at E:\todo-with-aptos\sources\todolist.move:55:13+9
    $temp_0'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList' := $Dereference($t9);
    assume {:print "$track_local(67,0,4):", $temp_0'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList'} $temp_0'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList' == $temp_0'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList';

    // $t10 := get_field<todolist::TodoList>.tasks($t9) at E:\todo-with-aptos\sources\todolist.move:56:33+16
    assume {:print "$at(2,2056,2072)"} true;
    $t10 := $Dereference($t9)->$tasks;

    // $t11 := table::contains<u64, todolist::Task>($t10, $t1) on_abort goto L10 with $t6 at E:\todo-with-aptos\sources\todolist.move:56:17+42
    call $t11 := $1_table_contains'u64_$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task'($t10, $t1);
    if ($abort_flag) {
        assume {:print "$at(2,2040,2082)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(67,0):", $t6} $t6 == $t6;
        goto L10;
    }

    // if ($t11) goto L4 else goto L3 at E:\todo-with-aptos\sources\todolist.move:56:9+71
    if ($t11) { goto L4; } else { goto L3; }

    // label L4 at E:\todo-with-aptos\sources\todolist.move:56:9+71
L4:

    // goto L5 at E:\todo-with-aptos\sources\todolist.move:56:9+71
    assume {:print "$at(2,2032,2103)"} true;
    goto L5;

    // label L3 at E:\todo-with-aptos\sources\todolist.move:56:9+71
L3:

    // destroy($t9) at E:\todo-with-aptos\sources\todolist.move:56:9+71
    assume {:print "$at(2,2032,2103)"} true;

    // $t12 := 2 at E:\todo-with-aptos\sources\todolist.move:56:61+18
    $t12 := 2;
    assume $IsValid'u64'($t12);

    // trace_abort($t12) at E:\todo-with-aptos\sources\todolist.move:56:9+71
    assume {:print "$at(2,2032,2103)"} true;
    assume {:print "$track_abort(67,0):", $t12} $t12 == $t12;

    // $t6 := move($t12) at E:\todo-with-aptos\sources\todolist.move:56:9+71
    $t6 := $t12;

    // goto L10 at E:\todo-with-aptos\sources\todolist.move:56:9+71
    goto L10;

    // label L5 at E:\todo-with-aptos\sources\todolist.move:57:51+9
    assume {:print "$at(2,2156,2165)"} true;
L5:

    // $t13 := borrow_field<todolist::TodoList>.tasks($t9) at E:\todo-with-aptos\sources\todolist.move:57:46+20
    assume {:print "$at(2,2151,2171)"} true;
    $t13 := $ChildMutation($t9, 0, $Dereference($t9)->$tasks);

    // $t14 := table::borrow_mut<u64, todolist::Task>($t13, $t1) on_abort goto L10 with $t6 at E:\todo-with-aptos\sources\todolist.move:57:28+48
    call $t14,$t13 := $1_table_borrow_mut'u64_$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task'($t13, $t1);
    if ($abort_flag) {
        assume {:print "$at(2,2133,2181)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(67,0):", $t6} $t6 == $t6;
        goto L10;
    }

    // trace_local[task_record]($t14) at E:\todo-with-aptos\sources\todolist.move:57:13+11
    $temp_0'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task' := $Dereference($t14);
    assume {:print "$track_local(67,0,3):", $temp_0'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task'} $temp_0'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task' == $temp_0'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task';

    // $t15 := get_field<todolist::Task>.completed($t14) at E:\todo-with-aptos\sources\todolist.move:58:17+21
    assume {:print "$at(2,2200,2221)"} true;
    $t15 := $Dereference($t14)->$completed;

    // $t16 := false at E:\todo-with-aptos\sources\todolist.move:58:42+5
    $t16 := false;
    assume $IsValid'bool'($t16);

    // $t17 := ==($t15, $t16) at E:\todo-with-aptos\sources\todolist.move:58:39+2
    $t17 := $IsEqual'bool'($t15, $t16);

    // if ($t17) goto L7 else goto L11 at E:\todo-with-aptos\sources\todolist.move:58:9+59
    if ($t17) { goto L7; } else { goto L11; }

    // label L7 at E:\todo-with-aptos\sources\todolist.move:58:9+59
L7:

    // goto L8 at E:\todo-with-aptos\sources\todolist.move:58:9+59
    assume {:print "$at(2,2192,2251)"} true;
    goto L8;

    // label L6 at E:\todo-with-aptos\sources\todolist.move:58:9+59
L6:

    // destroy($t14) at E:\todo-with-aptos\sources\todolist.move:58:9+59
    assume {:print "$at(2,2192,2251)"} true;

    // $t18 := 3 at E:\todo-with-aptos\sources\todolist.move:58:49+18
    $t18 := 3;
    assume $IsValid'u64'($t18);

    // trace_abort($t18) at E:\todo-with-aptos\sources\todolist.move:58:9+59
    assume {:print "$at(2,2192,2251)"} true;
    assume {:print "$track_abort(67,0):", $t18} $t18 == $t18;

    // $t6 := move($t18) at E:\todo-with-aptos\sources\todolist.move:58:9+59
    $t6 := $t18;

    // goto L10 at E:\todo-with-aptos\sources\todolist.move:58:9+59
    goto L10;

    // label L8 at E:\todo-with-aptos\sources\todolist.move:60:33+4
    assume {:print "$at(2,2288,2292)"} true;
L8:

    // $t19 := true at E:\todo-with-aptos\sources\todolist.move:60:33+4
    assume {:print "$at(2,2288,2292)"} true;
    $t19 := true;
    assume $IsValid'bool'($t19);

    // $t20 := borrow_field<todolist::Task>.completed($t14) at E:\todo-with-aptos\sources\todolist.move:60:9+21
    $t20 := $ChildMutation($t14, 3, $Dereference($t14)->$completed);

    // write_ref($t20, $t19) at E:\todo-with-aptos\sources\todolist.move:60:9+28
    $t20 := $UpdateMutation($t20, $t19);

    // write_back[Reference($t14).completed (bool)]($t20) at E:\todo-with-aptos\sources\todolist.move:60:9+28
    $t14 := $UpdateMutation($t14, $Update'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task'_completed($Dereference($t14), $Dereference($t20)));

    // write_back[Reference($t13)[]]($t14) at E:\todo-with-aptos\sources\todolist.move:60:9+28
    $t13 := $UpdateMutation($t13, UpdateTable($Dereference($t13), ReadVec($t14->p, LenVec($t13->p)), $Dereference($t14)));

    // write_back[Reference($t9).tasks (table::Table<u64, todolist::Task>)]($t13) at E:\todo-with-aptos\sources\todolist.move:60:9+28
    $t9 := $UpdateMutation($t9, $Update'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList'_tasks($Dereference($t9), $Dereference($t13)));

    // write_back[todolist::TodoList@]($t9) at E:\todo-with-aptos\sources\todolist.move:60:9+28
    $747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList_$memory := $ResourceUpdate($747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList_$memory, $GlobalLocationAddress($t9),
        $Dereference($t9));

    // label L9 at E:\todo-with-aptos\sources\todolist.move:62:5+1
    assume {:print "$at(2,2301,2302)"} true;
L9:

    // return () at E:\todo-with-aptos\sources\todolist.move:62:5+1
    assume {:print "$at(2,2301,2302)"} true;
    return;

    // label L10 at E:\todo-with-aptos\sources\todolist.move:62:5+1
L10:

    // abort($t6) at E:\todo-with-aptos\sources\todolist.move:62:5+1
    assume {:print "$at(2,2301,2302)"} true;
    $abort_code := $t6;
    $abort_flag := true;
    return;

    // label L11 at <internal>:1:1+10
    assume {:print "$at(1,0,10)"} true;
L11:

    // destroy($t9) at <internal>:1:1+10
    assume {:print "$at(1,0,10)"} true;

    // destroy($t13) at <internal>:1:1+10

    // goto L6 at <internal>:1:1+10
    goto L6;

}

// fun todolist::create_list [verification] at E:\todo-with-aptos\sources\todolist.move:25:5+283
procedure {:timeLimit 40} $747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_create_list$verify(_$t0: $signer) returns ()
{
    // declare local variables
    var $t1: $747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList;
    var $t2: Table int ($747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task);
    var $t3: int;
    var $t4: int;
    var $t5: $1_account_Account;
    var $t6: $1_event_EventHandle'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task';
    var $t7: int;
    var $t8: $747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList;
    var $t0: $signer;
    var $temp_0'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList': $747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList;
    var $temp_0'signer': $signer;
    $t0 := _$t0;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at E:\todo-with-aptos\sources\todolist.move:25:5+1
    assume {:print "$at(2,674,675)"} true;
    assume $IsValid'signer'($t0) && $1_signer_is_txn_signer($t0) && $1_signer_is_txn_signer_addr($t0->$addr);

    // assume forall $rsc: account::Account: ResourceDomain<account::Account>(): And(WellFormed($rsc), And(Le(Len<address>(select option::Option.vec(select account::CapabilityOffer.for(select account::Account.rotation_capability_offer($rsc)))), 1), Le(Len<address>(select option::Option.vec(select account::CapabilityOffer.for(select account::Account.signer_capability_offer($rsc)))), 1))) at E:\todo-with-aptos\sources\todolist.move:25:5+1
    assume (forall $a_0: int :: {$ResourceValue($1_account_Account_$memory, $a_0)}(var $rsc := $ResourceValue($1_account_Account_$memory, $a_0);
    (($IsValid'$1_account_Account'($rsc) && ((LenVec($rsc->$rotation_capability_offer->$for->$vec) <= 1) && (LenVec($rsc->$signer_capability_offer->$for->$vec) <= 1))))));

    // assume forall $rsc: todolist::TodoList: ResourceDomain<todolist::TodoList>(): WellFormed($rsc) at E:\todo-with-aptos\sources\todolist.move:25:5+1
    assume (forall $a_0: int :: {$ResourceValue($747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList_$memory, $a_0)}(var $rsc := $ResourceValue($747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList_$memory, $a_0);
    ($IsValid'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList'($rsc))));

    // trace_local[account]($t0) at E:\todo-with-aptos\sources\todolist.move:25:5+1
    assume {:print "$track_local(67,1,0):", $t0} $t0 == $t0;

    // $t2 := table::new<u64, todolist::Task>() on_abort goto L2 with $t3 at E:\todo-with-aptos\sources\todolist.move:27:20+12
    assume {:print "$at(2,783,795)"} true;
    call $t2 := $1_table_new'u64_$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task'();
    if ($abort_flag) {
        assume {:print "$at(2,783,795)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(67,1):", $t3} $t3 == $t3;
        goto L2;
    }

    // assume Identical($t4, signer::$address_of($t0)) at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\sources\account.spec.move:638:9+39
    assume {:print "$at(82,31785,31824)"} true;
    assume ($t4 == $1_signer_$address_of($t0));

    // assume Identical($t5, global<account::Account>($t4)) at E:\todo-with-aptos\./aptos-core/aptos-move/framework/aptos-framework\sources\account.spec.move:639:9+36
    assume {:print "$at(82,31833,31869)"} true;
    assume ($t5 == $ResourceValue($1_account_Account_$memory, $t4));

    // $t6 := account::new_event_handle<todolist::Task>($t0) on_abort goto L2 with $t3 at E:\todo-with-aptos\sources\todolist.move:28:29+41
    assume {:print "$at(2,826,867)"} true;
    call $t6 := $1_account_new_event_handle'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task'($t0);
    if ($abort_flag) {
        assume {:print "$at(2,826,867)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(67,1):", $t3} $t3 == $t3;
        goto L2;
    }

    // $t7 := 0 at E:\todo-with-aptos\sources\todolist.move:29:27+1
    assume {:print "$at(2,896,897)"} true;
    $t7 := 0;
    assume $IsValid'u64'($t7);

    // $t8 := pack todolist::TodoList($t2, $t6, $t7) at E:\todo-with-aptos\sources\todolist.move:26:28+156
    assume {:print "$at(2,752,908)"} true;
    $t8 := $747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList($t2, $t6, $t7);

    // trace_local[tasks_holder]($t8) at E:\todo-with-aptos\sources\todolist.move:26:13+12
    assume {:print "$track_local(67,1,1):", $t8} $t8 == $t8;

    // move_to<todolist::TodoList>($t8, $t0) on_abort goto L2 with $t3 at E:\todo-with-aptos\sources\todolist.move:31:9+7
    assume {:print "$at(2,919,926)"} true;
    if ($ResourceExists($747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList_$memory, $t0->$addr)) {
        call $ExecFailureAbort();
    } else {
        $747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList_$memory := $ResourceUpdate($747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList_$memory, $t0->$addr, $t8);
    }
    if ($abort_flag) {
        assume {:print "$at(2,919,926)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(67,1):", $t3} $t3 == $t3;
        goto L2;
    }

    // label L1 at E:\todo-with-aptos\sources\todolist.move:32:5+1
    assume {:print "$at(2,956,957)"} true;
L1:

    // return () at E:\todo-with-aptos\sources\todolist.move:32:5+1
    assume {:print "$at(2,956,957)"} true;
    return;

    // label L2 at E:\todo-with-aptos\sources\todolist.move:32:5+1
L2:

    // abort($t3) at E:\todo-with-aptos\sources\todolist.move:32:5+1
    assume {:print "$at(2,956,957)"} true;
    $abort_code := $t3;
    $abort_flag := true;
    return;

}

// fun todolist::create_task [verification] at E:\todo-with-aptos\sources\todolist.move:33:5+771
procedure {:timeLimit 40} $747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_create_task$verify(_$t0: $signer, _$t1: $1_string_String) returns ()
{
    // declare local variables
    var $t2: int;
    var $t3: $747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task;
    var $t4: int;
    var $t5: $Mutation ($747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList);
    var $t6: int;
    var $t7: int;
    var $t8: bool;
    var $t9: int;
    var $t10: $Mutation ($747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList);
    var $t11: int;
    var $t12: int;
    var $t13: int;
    var $t14: bool;
    var $t15: $747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task;
    var $t16: $Mutation (Table int ($747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task));
    var $t17: $Mutation (int);
    var $t18: $Mutation ($747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList);
    var $t19: $Mutation ($1_event_EventHandle'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task');
    var $t0: $signer;
    var $t1: $1_string_String;
    var $temp_0'$1_string_String': $1_string_String;
    var $temp_0'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task': $747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task;
    var $temp_0'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList': $747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList;
    var $temp_0'address': int;
    var $temp_0'signer': $signer;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at E:\todo-with-aptos\sources\todolist.move:33:5+1
    assume {:print "$at(2,963,964)"} true;
    assume $IsValid'signer'($t0) && $1_signer_is_txn_signer($t0) && $1_signer_is_txn_signer_addr($t0->$addr);

    // assume WellFormed($t1) at E:\todo-with-aptos\sources\todolist.move:33:5+1
    assume $IsValid'$1_string_String'($t1);

    // assume forall $rsc: todolist::TodoList: ResourceDomain<todolist::TodoList>(): WellFormed($rsc) at E:\todo-with-aptos\sources\todolist.move:33:5+1
    assume (forall $a_0: int :: {$ResourceValue($747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList_$memory, $a_0)}(var $rsc := $ResourceValue($747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList_$memory, $a_0);
    ($IsValid'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList'($rsc))));

    // trace_local[account]($t0) at E:\todo-with-aptos\sources\todolist.move:33:5+1
    assume {:print "$track_local(67,2,0):", $t0} $t0 == $t0;

    // trace_local[content]($t1) at E:\todo-with-aptos\sources\todolist.move:33:5+1
    assume {:print "$track_local(67,2,1):", $t1} $t1 == $t1;

    // $t6 := signer::address_of($t0) on_abort goto L4 with $t7 at E:\todo-with-aptos\sources\todolist.move:34:30+27
    assume {:print "$at(2,1077,1104)"} true;
    call $t6 := $1_signer_address_of($t0);
    if ($abort_flag) {
        assume {:print "$at(2,1077,1104)"} true;
        $t7 := $abort_code;
        assume {:print "$track_abort(67,2):", $t7} $t7 == $t7;
        goto L4;
    }

    // trace_local[signer_address]($t6) at E:\todo-with-aptos\sources\todolist.move:34:13+14
    assume {:print "$track_local(67,2,4):", $t6} $t6 == $t6;

    // $t8 := exists<todolist::TodoList>($t6) at E:\todo-with-aptos\sources\todolist.move:35:17+6
    assume {:print "$at(2,1123,1129)"} true;
    $t8 := $ResourceExists($747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList_$memory, $t6);

    // if ($t8) goto L1 else goto L0 at E:\todo-with-aptos\sources\todolist.move:35:9+60
    if ($t8) { goto L1; } else { goto L0; }

    // label L1 at E:\todo-with-aptos\sources\todolist.move:35:9+60
L1:

    // goto L2 at E:\todo-with-aptos\sources\todolist.move:35:9+60
    assume {:print "$at(2,1115,1175)"} true;
    goto L2;

    // label L0 at E:\todo-with-aptos\sources\todolist.move:35:51+17
L0:

    // $t9 := 1 at E:\todo-with-aptos\sources\todolist.move:35:51+17
    assume {:print "$at(2,1157,1174)"} true;
    $t9 := 1;
    assume $IsValid'u64'($t9);

    // trace_abort($t9) at E:\todo-with-aptos\sources\todolist.move:35:9+60
    assume {:print "$at(2,1115,1175)"} true;
    assume {:print "$track_abort(67,2):", $t9} $t9 == $t9;

    // $t7 := move($t9) at E:\todo-with-aptos\sources\todolist.move:35:9+60
    $t7 := $t9;

    // goto L4 at E:\todo-with-aptos\sources\todolist.move:35:9+60
    goto L4;

    // label L2 at E:\todo-with-aptos\sources\todolist.move:36:53+14
    assume {:print "$at(2,1230,1244)"} true;
L2:

    // $t10 := borrow_global<todolist::TodoList>($t6) on_abort goto L4 with $t7 at E:\todo-with-aptos\sources\todolist.move:36:25+17
    assume {:print "$at(2,1202,1219)"} true;
    if (!$ResourceExists($747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList_$memory, $t6)) {
        call $ExecFailureAbort();
    } else {
        $t10 := $Mutation($Global($t6), EmptyVec(), $ResourceValue($747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList_$memory, $t6));
    }
    if ($abort_flag) {
        assume {:print "$at(2,1202,1219)"} true;
        $t7 := $abort_code;
        assume {:print "$track_abort(67,2):", $t7} $t7 == $t7;
        goto L4;
    }

    // trace_local[todo_list]($t10) at E:\todo-with-aptos\sources\todolist.move:36:13+9
    $temp_0'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList' := $Dereference($t10);
    assume {:print "$track_local(67,2,5):", $temp_0'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList'} $temp_0'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList' == $temp_0'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList';

    // $t11 := get_field<todolist::TodoList>.task_counter($t10) at E:\todo-with-aptos\sources\todolist.move:37:23+22
    assume {:print "$at(2,1270,1292)"} true;
    $t11 := $Dereference($t10)->$task_counter;

    // $t12 := 1 at E:\todo-with-aptos\sources\todolist.move:37:48+1
    $t12 := 1;
    assume $IsValid'u64'($t12);

    // $t13 := +($t11, $t12) on_abort goto L4 with $t7 at E:\todo-with-aptos\sources\todolist.move:37:46+1
    call $t13 := $AddU64($t11, $t12);
    if ($abort_flag) {
        assume {:print "$at(2,1293,1294)"} true;
        $t7 := $abort_code;
        assume {:print "$track_abort(67,2):", $t7} $t7 == $t7;
        goto L4;
    }

    // trace_local[counter]($t13) at E:\todo-with-aptos\sources\todolist.move:37:13+7
    assume {:print "$track_local(67,2,2):", $t13} $t13 == $t13;

    // $t14 := false at E:\todo-with-aptos\sources\todolist.move:42:24+5
    assume {:print "$at(2,1453,1458)"} true;
    $t14 := false;
    assume $IsValid'bool'($t14);

    // $t15 := pack todolist::Task($t13, $t6, $t1, $t14) at E:\todo-with-aptos\sources\todolist.move:38:24+147
    assume {:print "$at(2,1322,1469)"} true;
    $t15 := $747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task($t13, $t6, $t1, $t14);

    // trace_local[new_task]($t15) at E:\todo-with-aptos\sources\todolist.move:38:13+8
    assume {:print "$track_local(67,2,3):", $t15} $t15 == $t15;

    // $t16 := borrow_field<todolist::TodoList>.tasks($t10) at E:\todo-with-aptos\sources\todolist.move:45:23+20
    assume {:print "$at(2,1496,1516)"} true;
    $t16 := $ChildMutation($t10, 0, $Dereference($t10)->$tasks);

    // table::upsert<u64, todolist::Task>($t16, $t13, $t15) on_abort goto L4 with $t7 at E:\todo-with-aptos\sources\todolist.move:45:9+54
    call $t16 := $1_table_upsert'u64_$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task'($t16, $t13, $t15);
    if ($abort_flag) {
        assume {:print "$at(2,1482,1536)"} true;
        $t7 := $abort_code;
        assume {:print "$track_abort(67,2):", $t7} $t7 == $t7;
        goto L4;
    }

    // write_back[Reference($t10).tasks (table::Table<u64, todolist::Task>)]($t16) at E:\todo-with-aptos\sources\todolist.move:45:9+54
    $t10 := $UpdateMutation($t10, $Update'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList'_tasks($Dereference($t10), $Dereference($t16)));

    // $t17 := borrow_field<todolist::TodoList>.task_counter($t10) at E:\todo-with-aptos\sources\todolist.move:46:9+22
    assume {:print "$at(2,1547,1569)"} true;
    $t17 := $ChildMutation($t10, 2, $Dereference($t10)->$task_counter);

    // write_ref($t17, $t13) at E:\todo-with-aptos\sources\todolist.move:46:9+32
    $t17 := $UpdateMutation($t17, $t13);

    // write_back[Reference($t10).task_counter (u64)]($t17) at E:\todo-with-aptos\sources\todolist.move:46:9+32
    $t10 := $UpdateMutation($t10, $Update'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList'_task_counter($Dereference($t10), $Dereference($t17)));

    // write_back[todolist::TodoList@]($t10) at E:\todo-with-aptos\sources\todolist.move:46:9+32
    $747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList_$memory := $ResourceUpdate($747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList_$memory, $GlobalLocationAddress($t10),
        $Dereference($t10));

    // $t18 := borrow_global<todolist::TodoList>($t6) on_abort goto L4 with $t7 at E:\todo-with-aptos\sources\todolist.move:48:18+17
    assume {:print "$at(2,1633,1650)"} true;
    if (!$ResourceExists($747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList_$memory, $t6)) {
        call $ExecFailureAbort();
    } else {
        $t18 := $Mutation($Global($t6), EmptyVec(), $ResourceValue($747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList_$memory, $t6));
    }
    if ($abort_flag) {
        assume {:print "$at(2,1633,1650)"} true;
        $t7 := $abort_code;
        assume {:print "$track_abort(67,2):", $t7} $t7 == $t7;
        goto L4;
    }

    // $t19 := borrow_field<todolist::TodoList>.set_task_event($t18) at E:\todo-with-aptos\sources\todolist.move:48:13+63
    $t19 := $ChildMutation($t18, 1, $Dereference($t18)->$set_task_event);

    // opaque begin: event::emit_event<todolist::Task>($t19, $t15) at E:\todo-with-aptos\sources\todolist.move:47:9+136
    assume {:print "$at(2,1590,1726)"} true;

    // opaque end: event::emit_event<todolist::Task>($t19, $t15) at E:\todo-with-aptos\sources\todolist.move:47:9+136

    // write_back[Reference($t18).set_task_event (event::EventHandle<todolist::Task>)]($t19) at E:\todo-with-aptos\sources\todolist.move:47:9+136
    $t18 := $UpdateMutation($t18, $Update'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList'_set_task_event($Dereference($t18), $Dereference($t19)));

    // write_back[todolist::TodoList@]($t18) at E:\todo-with-aptos\sources\todolist.move:47:9+136
    $747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList_$memory := $ResourceUpdate($747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList_$memory, $GlobalLocationAddress($t18),
        $Dereference($t18));

    // label L3 at E:\todo-with-aptos\sources\todolist.move:51:5+1
    assume {:print "$at(2,1733,1734)"} true;
L3:

    // return () at E:\todo-with-aptos\sources\todolist.move:51:5+1
    assume {:print "$at(2,1733,1734)"} true;
    return;

    // label L4 at E:\todo-with-aptos\sources\todolist.move:51:5+1
L4:

    // abort($t7) at E:\todo-with-aptos\sources\todolist.move:51:5+1
    assume {:print "$at(2,1733,1734)"} true;
    $abort_code := $t7;
    $abort_flag := true;
    return;

}

// fun todolist::discomplete_task [verification] at E:\todo-with-aptos\sources\todolist.move:63:5+534
procedure {:timeLimit 40} $747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_discomplete_task$verify(_$t0: $signer, _$t1: int) returns ()
{
    // declare local variables
    var $t2: int;
    var $t3: $Mutation ($747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task);
    var $t4: $Mutation ($747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList);
    var $t5: int;
    var $t6: int;
    var $t7: bool;
    var $t8: int;
    var $t9: $Mutation ($747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList);
    var $t10: Table int ($747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task);
    var $t11: bool;
    var $t12: int;
    var $t13: $Mutation (Table int ($747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task));
    var $t14: $Mutation ($747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task);
    var $t15: bool;
    var $t16: bool;
    var $t17: bool;
    var $t18: int;
    var $t19: bool;
    var $t20: $Mutation (bool);
    var $t0: $signer;
    var $t1: int;
    var $temp_0'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task': $747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task;
    var $temp_0'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList': $747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList;
    var $temp_0'address': int;
    var $temp_0'signer': $signer;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at E:\todo-with-aptos\sources\todolist.move:63:5+1
    assume {:print "$at(2,2308,2309)"} true;
    assume $IsValid'signer'($t0) && $1_signer_is_txn_signer($t0) && $1_signer_is_txn_signer_addr($t0->$addr);

    // assume WellFormed($t1) at E:\todo-with-aptos\sources\todolist.move:63:5+1
    assume $IsValid'u64'($t1);

    // assume forall $rsc: todolist::TodoList: ResourceDomain<todolist::TodoList>(): WellFormed($rsc) at E:\todo-with-aptos\sources\todolist.move:63:5+1
    assume (forall $a_0: int :: {$ResourceValue($747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList_$memory, $a_0)}(var $rsc := $ResourceValue($747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList_$memory, $a_0);
    ($IsValid'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList'($rsc))));

    // trace_local[account]($t0) at E:\todo-with-aptos\sources\todolist.move:63:5+1
    assume {:print "$track_local(67,3,0):", $t0} $t0 == $t0;

    // trace_local[task_id]($t1) at E:\todo-with-aptos\sources\todolist.move:63:5+1
    assume {:print "$track_local(67,3,1):", $t1} $t1 == $t1;

    // $t5 := signer::address_of($t0) on_abort goto L10 with $t6 at E:\todo-with-aptos\sources\todolist.move:64:30+27
    assume {:print "$at(2,2424,2451)"} true;
    call $t5 := $1_signer_address_of($t0);
    if ($abort_flag) {
        assume {:print "$at(2,2424,2451)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(67,3):", $t6} $t6 == $t6;
        goto L10;
    }

    // trace_local[signer_address]($t5) at E:\todo-with-aptos\sources\todolist.move:64:13+14
    assume {:print "$track_local(67,3,2):", $t5} $t5 == $t5;

    // $t7 := exists<todolist::TodoList>($t5) at E:\todo-with-aptos\sources\todolist.move:65:17+6
    assume {:print "$at(2,2470,2476)"} true;
    $t7 := $ResourceExists($747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList_$memory, $t5);

    // if ($t7) goto L1 else goto L0 at E:\todo-with-aptos\sources\todolist.move:65:9+44
    if ($t7) { goto L1; } else { goto L0; }

    // label L1 at E:\todo-with-aptos\sources\todolist.move:65:9+44
L1:

    // goto L2 at E:\todo-with-aptos\sources\todolist.move:65:9+44
    assume {:print "$at(2,2462,2506)"} true;
    goto L2;

    // label L0 at E:\todo-with-aptos\sources\todolist.move:65:51+1
L0:

    // $t8 := 1 at E:\todo-with-aptos\sources\todolist.move:65:51+1
    assume {:print "$at(2,2504,2505)"} true;
    $t8 := 1;
    assume $IsValid'u64'($t8);

    // trace_abort($t8) at E:\todo-with-aptos\sources\todolist.move:65:9+44
    assume {:print "$at(2,2462,2506)"} true;
    assume {:print "$track_abort(67,3):", $t8} $t8 == $t8;

    // $t6 := move($t8) at E:\todo-with-aptos\sources\todolist.move:65:9+44
    $t6 := $t8;

    // goto L10 at E:\todo-with-aptos\sources\todolist.move:65:9+44
    goto L10;

    // label L2 at E:\todo-with-aptos\sources\todolist.move:66:53+14
    assume {:print "$at(2,2561,2575)"} true;
L2:

    // $t9 := borrow_global<todolist::TodoList>($t5) on_abort goto L10 with $t6 at E:\todo-with-aptos\sources\todolist.move:66:25+17
    assume {:print "$at(2,2533,2550)"} true;
    if (!$ResourceExists($747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList_$memory, $t5)) {
        call $ExecFailureAbort();
    } else {
        $t9 := $Mutation($Global($t5), EmptyVec(), $ResourceValue($747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList_$memory, $t5));
    }
    if ($abort_flag) {
        assume {:print "$at(2,2533,2550)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(67,3):", $t6} $t6 == $t6;
        goto L10;
    }

    // trace_local[todo_list]($t9) at E:\todo-with-aptos\sources\todolist.move:66:13+9
    $temp_0'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList' := $Dereference($t9);
    assume {:print "$track_local(67,3,4):", $temp_0'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList'} $temp_0'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList' == $temp_0'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList';

    // $t10 := get_field<todolist::TodoList>.tasks($t9) at E:\todo-with-aptos\sources\todolist.move:67:33+16
    assume {:print "$at(2,2611,2627)"} true;
    $t10 := $Dereference($t9)->$tasks;

    // $t11 := table::contains<u64, todolist::Task>($t10, $t1) on_abort goto L10 with $t6 at E:\todo-with-aptos\sources\todolist.move:67:17+42
    call $t11 := $1_table_contains'u64_$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task'($t10, $t1);
    if ($abort_flag) {
        assume {:print "$at(2,2595,2637)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(67,3):", $t6} $t6 == $t6;
        goto L10;
    }

    // if ($t11) goto L4 else goto L3 at E:\todo-with-aptos\sources\todolist.move:67:9+54
    if ($t11) { goto L4; } else { goto L3; }

    // label L4 at E:\todo-with-aptos\sources\todolist.move:67:9+54
L4:

    // goto L5 at E:\todo-with-aptos\sources\todolist.move:67:9+54
    assume {:print "$at(2,2587,2641)"} true;
    goto L5;

    // label L3 at E:\todo-with-aptos\sources\todolist.move:67:9+54
L3:

    // destroy($t9) at E:\todo-with-aptos\sources\todolist.move:67:9+54
    assume {:print "$at(2,2587,2641)"} true;

    // $t12 := 2 at E:\todo-with-aptos\sources\todolist.move:67:61+1
    $t12 := 2;
    assume $IsValid'u64'($t12);

    // trace_abort($t12) at E:\todo-with-aptos\sources\todolist.move:67:9+54
    assume {:print "$at(2,2587,2641)"} true;
    assume {:print "$track_abort(67,3):", $t12} $t12 == $t12;

    // $t6 := move($t12) at E:\todo-with-aptos\sources\todolist.move:67:9+54
    $t6 := $t12;

    // goto L10 at E:\todo-with-aptos\sources\todolist.move:67:9+54
    goto L10;

    // label L5 at E:\todo-with-aptos\sources\todolist.move:68:51+9
    assume {:print "$at(2,2694,2703)"} true;
L5:

    // $t13 := borrow_field<todolist::TodoList>.tasks($t9) at E:\todo-with-aptos\sources\todolist.move:68:46+20
    assume {:print "$at(2,2689,2709)"} true;
    $t13 := $ChildMutation($t9, 0, $Dereference($t9)->$tasks);

    // $t14 := table::borrow_mut<u64, todolist::Task>($t13, $t1) on_abort goto L10 with $t6 at E:\todo-with-aptos\sources\todolist.move:68:28+48
    call $t14,$t13 := $1_table_borrow_mut'u64_$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task'($t13, $t1);
    if ($abort_flag) {
        assume {:print "$at(2,2671,2719)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(67,3):", $t6} $t6 == $t6;
        goto L10;
    }

    // trace_local[task_record]($t14) at E:\todo-with-aptos\sources\todolist.move:68:13+11
    $temp_0'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task' := $Dereference($t14);
    assume {:print "$track_local(67,3,3):", $temp_0'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task'} $temp_0'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task' == $temp_0'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task';

    // $t15 := get_field<todolist::Task>.completed($t14) at E:\todo-with-aptos\sources\todolist.move:69:17+21
    assume {:print "$at(2,2738,2759)"} true;
    $t15 := $Dereference($t14)->$completed;

    // $t16 := true at E:\todo-with-aptos\sources\todolist.move:69:42+4
    $t16 := true;
    assume $IsValid'bool'($t16);

    // $t17 := ==($t15, $t16) at E:\todo-with-aptos\sources\todolist.move:69:39+2
    $t17 := $IsEqual'bool'($t15, $t16);

    // if ($t17) goto L7 else goto L11 at E:\todo-with-aptos\sources\todolist.move:69:9+62
    if ($t17) { goto L7; } else { goto L11; }

    // label L7 at E:\todo-with-aptos\sources\todolist.move:69:9+62
L7:

    // goto L8 at E:\todo-with-aptos\sources\todolist.move:69:9+62
    assume {:print "$at(2,2730,2792)"} true;
    goto L8;

    // label L6 at E:\todo-with-aptos\sources\todolist.move:69:9+62
L6:

    // destroy($t14) at E:\todo-with-aptos\sources\todolist.move:69:9+62
    assume {:print "$at(2,2730,2792)"} true;

    // $t18 := 4 at E:\todo-with-aptos\sources\todolist.move:69:48+22
    $t18 := 4;
    assume $IsValid'u64'($t18);

    // trace_abort($t18) at E:\todo-with-aptos\sources\todolist.move:69:9+62
    assume {:print "$at(2,2730,2792)"} true;
    assume {:print "$track_abort(67,3):", $t18} $t18 == $t18;

    // $t6 := move($t18) at E:\todo-with-aptos\sources\todolist.move:69:9+62
    $t6 := $t18;

    // goto L10 at E:\todo-with-aptos\sources\todolist.move:69:9+62
    goto L10;

    // label L8 at E:\todo-with-aptos\sources\todolist.move:71:33+5
    assume {:print "$at(2,2829,2834)"} true;
L8:

    // $t19 := false at E:\todo-with-aptos\sources\todolist.move:71:33+5
    assume {:print "$at(2,2829,2834)"} true;
    $t19 := false;
    assume $IsValid'bool'($t19);

    // $t20 := borrow_field<todolist::Task>.completed($t14) at E:\todo-with-aptos\sources\todolist.move:71:9+21
    $t20 := $ChildMutation($t14, 3, $Dereference($t14)->$completed);

    // write_ref($t20, $t19) at E:\todo-with-aptos\sources\todolist.move:71:9+29
    $t20 := $UpdateMutation($t20, $t19);

    // write_back[Reference($t14).completed (bool)]($t20) at E:\todo-with-aptos\sources\todolist.move:71:9+29
    $t14 := $UpdateMutation($t14, $Update'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_Task'_completed($Dereference($t14), $Dereference($t20)));

    // write_back[Reference($t13)[]]($t14) at E:\todo-with-aptos\sources\todolist.move:71:9+29
    $t13 := $UpdateMutation($t13, UpdateTable($Dereference($t13), ReadVec($t14->p, LenVec($t13->p)), $Dereference($t14)));

    // write_back[Reference($t9).tasks (table::Table<u64, todolist::Task>)]($t13) at E:\todo-with-aptos\sources\todolist.move:71:9+29
    $t9 := $UpdateMutation($t9, $Update'$747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList'_tasks($Dereference($t9), $Dereference($t13)));

    // write_back[todolist::TodoList@]($t9) at E:\todo-with-aptos\sources\todolist.move:71:9+29
    $747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList_$memory := $ResourceUpdate($747a2c84552e69257be49b20683f205847ad69f7d367a729bc81aed1496ec6de_todolist_TodoList_$memory, $GlobalLocationAddress($t9),
        $Dereference($t9));

    // label L9 at E:\todo-with-aptos\sources\todolist.move:72:5+1
    assume {:print "$at(2,2841,2842)"} true;
L9:

    // return () at E:\todo-with-aptos\sources\todolist.move:72:5+1
    assume {:print "$at(2,2841,2842)"} true;
    return;

    // label L10 at E:\todo-with-aptos\sources\todolist.move:72:5+1
L10:

    // abort($t6) at E:\todo-with-aptos\sources\todolist.move:72:5+1
    assume {:print "$at(2,2841,2842)"} true;
    $abort_code := $t6;
    $abort_flag := true;
    return;

    // label L11 at <internal>:1:1+10
    assume {:print "$at(1,0,10)"} true;
L11:

    // destroy($t9) at <internal>:1:1+10
    assume {:print "$at(1,0,10)"} true;

    // destroy($t13) at <internal>:1:1+10

    // goto L6 at <internal>:1:1+10
    goto L6;

}
