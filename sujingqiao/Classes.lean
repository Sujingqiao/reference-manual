```lean
structure Vegetable where
  color : String
  size : Fin 5
deriving Ord
```
```lean
def broccoli : Vegetable where
  color := "green"
  size := 2

def sweetPotato : Vegetable where
  color := "orange"
  size := 3
```
```lean
instance : LT Vegetable := ltOfOrd
instance : LE Vegetable := leOfOrd
```
```lean (name := brLtSw)
#eval broccoli < sweetPotato
```
```leanOutput brLtSw
true
```
```leanOutput brLtSw
true
```
```lean (name := brLeSw)
#eval broccoli ≤ sweetPotato
```
```leanOutput brLeSw
true
```
```leanOutput brLeSw
true
```
```lean (name := brLtBr)
#eval broccoli < broccoli
```
```leanOutput brLtBr
false
```
```leanOutput brLtBr
false
```
```lean (name := brLeBr)
#eval broccoli ≤ broccoli
```
```leanOutput brLeBr
true
```
```leanOutput brLeBr
true
```
```lean -show
variable {α : Type u} [LE α]
```
```lean +error (name := NatFunNotDecEq)
example (f g : Nat → Nat) : Decidable (f = g) := inferInstance
```
```leanOutput NatFunNotDecEq
failed to synthesize
  Decidable (f = g)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```
```leanOutput NatFunNotDecEq
failed to synthesize
  Decidable (f = g)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```
```lean
open Classical
noncomputable example (f g : Nat → Nat) : Decidable (f = g) := inferInstance
``````lean
class IsEnum (α : Type) where
  size : Nat
  toIdx : α → Fin size
  fromIdx : Fin size → α
  to_from_id : ∀ (i : Fin size), toIdx (fromIdx i) = i
  from_to_id : ∀ (x : α), fromIdx (toIdx x) = x
```
```lean
instance : IsEnum Bool where
  size := 2
  toIdx
    | false => 0
    | true => 1
  fromIdx
    | 0 => false
    | 1 => true
  to_from_id
    | 0 => rfl
    | 1 => rfl
  from_to_id
    | false => rfl
    | true => rfl
```
```lean
open Lean Elab Parser Term Command

def deriveIsEnum (declNames : Array Name) : CommandElabM Bool := do
  if h : declNames.size = 1 then
    let env ← getEnv
    if let some (.inductInfo ind) := env.find? declNames[0] then
      let mut tos : Array (TSyntax ``matchAlt) := #[]
      let mut froms := #[]
      let mut to_froms := #[]
      let mut from_tos := #[]
      let mut i := 0

      for ctorName in ind.ctors do
        let c := mkIdent ctorName
        let n := Syntax.mkNumLit (toString i)

        tos      := tos.push      (← `(matchAltExpr| | $c => $n))
        from_tos := from_tos.push (← `(matchAltExpr| | $c => rfl))
        froms    := froms.push    (← `(matchAltExpr| | $n => $c))
        to_froms := to_froms.push (← `(matchAltExpr| | $n => rfl))

        i := i + 1

      let cmd ← `(instance : IsEnum $(mkIdent declNames[0]) where
                    size := $(quote ind.ctors.length)
                    toIdx $tos:matchAlt*
                    fromIdx $froms:matchAlt*
                    to_from_id $to_froms:matchAlt*
                    from_to_id $from_tos:matchAlt*)
      elabCommand cmd

      return true
  return false

initialize
  registerDerivingHandler ``IsEnum deriveIsEnum
``````lean
structure NatWrapper where
  val : Nat

instance : BEq NatWrapper where
  beq
    | ⟨x⟩, ⟨y⟩ => x == y
```
```lean
structure NatWrapper where
  val : Nat
```
```lean
instance : BEq NatWrapper where
  beq
    | ⟨x⟩, ⟨y⟩ => x == y

instance : BEq NatWrapper :=
  ⟨fun x y => x.val == y.val⟩

instance : BEq NatWrapper :=
  ⟨fun ⟨x⟩ ⟨y⟩ => x == y⟩
```
```lean
@[instance]
def instBeqNatWrapper : BEq NatWrapper where
  beq
    | ⟨x⟩, ⟨y⟩ => x == y

instance : BEq NatWrapper :=
  ⟨fun x y => x.val == y.val⟩

instance : BEq NatWrapper :=
  ⟨fun ⟨x⟩ ⟨y⟩ => x == y⟩
```
```lean
inductive NatTree where
  | leaf
  | branch (left : NatTree) (val : Nat) (right : NatTree)
```
```lean +error (name := beqNatTreeFail)
instance : BEq NatTree where
  beq
    | .leaf, .leaf => true
    | .branch l1 v1 r1, .branch l2 v2 r2 => l1 == l2 && v1 == v2 && r1 == r2
    | _, _ => false
```
```leanOutput beqNatTreeFail
failed to synthesize
  BEq NatTree

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```
```leanOutput beqNatTreeFail
failed to synthesize
  BEq NatTree

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```
```lean
def NatTree.beq : NatTree → NatTree → Bool
  | .leaf, .leaf => true
  | .branch l1 v1 r1, .branch l2 v2 r2 => l1 == l2 && v1 == v2 && r1 == r2
  | _, _ => false
```
```lean
instance : BEq NatTree where
  beq := NatTree.beq
```
```lean
instance : BEq NatTree := ⟨NatTree.beq⟩
```
```lean
inductive NatRoseTree where
  | node (val : Nat) (children : Array NatRoseTree)

```
```lean +error (name := natRoseTreeBEqFail) -keep
def NatRoseTree.beq : (tree1 tree2 : NatRoseTree) → Bool
  | .node val1 children1, .node val2 children2 =>
    val1 == val2 &&
    children1 == children2
```
```leanOutput natRoseTreeBEqFail
failed to synthesize
  BEq (Array NatRoseTree)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```
```leanOutput natRoseTreeBEqFail
failed to synthesize
  BEq (Array NatRoseTree)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```
```lean
partial def NatRoseTree.beq : (tree1 tree2 : NatRoseTree) → Bool
  | .node val1 children1, .node val2 children2 =>
    let _ : BEq NatRoseTree := ⟨NatRoseTree.beq⟩
    val1 == val2 &&
    children1 == children2
```
```lean -show
axiom α : Type
```
```lean
inductive ThreeChoices where
  | yes | no | maybe

instance : DecidableEq ThreeChoices
  | .yes,   .yes   =>
    .isTrue rfl
  | .no,    .no    =>
    .isTrue rfl
  | .maybe, .maybe =>
    .isTrue rfl
  | .yes,   .maybe | .yes,   .no
  | .maybe, .yes   | .maybe, .no
  | .no,    .yes   | .no,    .maybe =>
    .isFalse nofun

```
```lean
inductive StringList where
  | nil
  | cons (hd : String) (tl : StringList)
```
```lean +error (name := stringListNoRec) -keep
instance : DecidableEq StringList
  | .nil, .nil => .isTrue rfl
  | .cons h1 t1, .cons h2 t2 =>
    if h : h1 = h2 then
      if h' : t1 = t2 then
        .isTrue (by simp [*])
      else
        .isFalse (by intro hEq; cases hEq; trivial)
    else
      .isFalse (by intro hEq; cases hEq; trivial)
  | .nil, .cons _ _ | .cons _ _, .nil => .isFalse nofun
```
```leanOutput stringListNoRec
failed to synthesize
  Decidable (t1 = t2)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```
```leanOutput stringListNoRec
failed to synthesize
  Decidable (t1 = t2)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```
```lean
instance instDecidableEqStringList : DecidableEq StringList
  | .nil, .nil => .isTrue rfl
  | .cons h1 t1, .cons h2 t2 =>
    let _ : Decidable (t1 = t2) :=
      instDecidableEqStringList t1 t2
    if h : h1 = h2 then
      if h' : t1 = t2 then
        .isTrue (by simp [*])
      else
        .isFalse (by intro hEq; cases hEq; trivial)
    else
      .isFalse (by intro hEq; cases hEq; trivial)
  | .nil, .cons _ _ | .cons _ _, .nil => .isFalse nofun
```
```lean
structure Even where
  half : Nat
```
```lean (name := insts)
instance ofNatEven0 : OfNat Even 0 where
  ofNat := ⟨0⟩

instance ofNatEvenPlusTwo [OfNat Even n] : OfNat Even (n + 2) where
  ofNat := ⟨(OfNat.ofNat n : Even).half + 1⟩

#eval (0 : Even)
#eval (34 : Even)
#eval (254 : Even)
```
```leanOutput insts
{ half := 0 }
```
```leanOutput insts
{ half := 0 }
```
```leanOutput insts
{ half := 17 }
```
```leanOutput insts
{ half := 17 }
```
```leanOutput insts
{ half := 127 }
```
```leanOutput insts
{ half := 127 }
```
```lean
attribute [default_instance 100] ofNatEven0
attribute [default_instance 100] ofNatEvenPlusTwo
```
```lean (name := withDefaults)
#eval 0
#eval 34
```
```leanOutput withDefaults
{ half := 0 }
```
```leanOutput withDefaults
{ half := 0 }
```
```leanOutput withDefaults
{ half := 17 }
```
```leanOutput withDefaults
{ half := 17 }
```
```lean (name := stillNat)
#eval 5
```
```leanOutput stillNat
5
```
```leanOutput stillNat
5
``````lean
structure NatPair where
  x : Nat
  y : Nat

def addPairs (p1 p2 : NatPair) : NatPair :=
  let _ : Add NatPair :=
    ⟨fun ⟨x1, y1⟩ ⟨x2, y2⟩ => ⟨x1 + x2, y1 + y2⟩⟩
  p1 + p2
```
```lean
structure NatPair where
  x : Nat
  y : Nat

instance : Add NatPair where
  add
    | ⟨x1, y1⟩, ⟨x2, y2⟩ => ⟨x1 + x2, y1 + y2⟩

def addPairs (p1 p2 : NatPair) : NatPair :=
  let _ : Add NatPair :=
    ⟨fun _ _ => ⟨0, 0⟩⟩
  p1 + p2
```
```lean (name:=addPairsOut)
#eval addPairs ⟨1, 2⟩ ⟨5, 2⟩
```
```leanOutput addPairsOut
{ x := 0, y := 0 }
```
```leanOutput addPairsOut
{ x := 0, y := 0 }
```
```lean
instance aNonemptySumInstance (α : Type) {β : Type} [inst : Nonempty α] : Nonempty (α ⊕ β) :=
  let ⟨x⟩ := inst
  ⟨.inl x⟩
```
```lean (name := instSearch)
set_option pp.explicit true in
#synth Nonempty (Nat ⊕ Empty)
```
```leanOutput instSearch
@aNonemptySumInstance Nat Empty (@instNonemptyOfInhabited Nat instInhabitedNat)
```
```leanOutput instSearch
@aNonemptySumInstance Nat Empty (@instNonemptyOfInhabited Nat instInhabitedNat)
```
```lean
class Serialize (input output : Type) where
  ser : input → output
export Serialize (ser)

instance : Serialize Nat String where
  ser n := toString n

instance [Serialize α γ] [Serialize β γ] [Append γ] :
    Serialize (α × β) γ where
  ser
    | (x, y) => ser x ++ ser y
```
```lean +error (name := noOutputType)
example := ser (2, 3)
```
```leanOutput noOutputType
typeclass instance problem is stuck, it is often due to metavariables
  Serialize (Nat × Nat) ?m.16
```
```leanOutput noOutputType
typeclass instance problem is stuck, it is often due to metavariables
  Serialize (Nat × Nat) ?m.16
```
```lean
example : String := ser (2, 3)
```
```lean
class Serialize (input : Type) (output : outParam Type) where
  ser : input → output
export Serialize (ser)

instance : Serialize Nat String where
  ser n := toString n

instance [Serialize α γ] [Serialize β γ] [Append γ] :
    Serialize (α × β) γ where
  ser
    | (x, y) => ser x ++ ser y
```
```lean
example := ser (2, 3)
```
```lean
class OneSmaller (α : Type) (β : outParam Type) where
  biggest : α
  shrink : (x : α) → x ≠ biggest → β

instance : OneSmaller (Option α) α where
  biggest := none
  shrink
    | some x, _ => x

instance : OneSmaller (Option Bool) (Option Unit) where
  biggest := some true
  shrink
    | none, _ => none
    | some false, _ => some ()

instance : OneSmaller Bool Unit where
  biggest := true
  shrink
    | false, _ => ()
```
```lean +error (name := nosmaller)
#check OneSmaller.shrink (β := Bool) (some false) sorry
```
```leanOutput nosmaller
failed to synthesize
  OneSmaller (Option Bool) Bool

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```
```leanOutput nosmaller
failed to synthesize
  OneSmaller (Option Bool) Bool

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```
```lean
class OneSmaller (α : Type) (β : semiOutParam Type) where
  biggest : α
  shrink : (x : α) → x ≠ biggest → β

instance : OneSmaller (Option α) α where
  biggest := none
  shrink
    | some x, _ => x

instance : OneSmaller (Option Bool) (Option Unit) where
  biggest := some true
  shrink
    | none, _ => none
    | some false, _ => some ()

instance : OneSmaller Bool Unit where
  biggest := true
  shrink
    | false, _ => ()
```
```lean (name := nosmaller2)
#check OneSmaller.shrink (β := Bool) (some false) sorry
```
```leanOutput nosmaller2
OneSmaller.shrink (some false) ⋯ : Bool
```
```leanOutput nosmaller2
OneSmaller.shrink (some false) ⋯ : Bool
``````lean -show
-- Always keep this in sync with the description below. It ensures that the list is complete.
/--
info: #[`package.barrel, `package.cache, `package.deps, `package.extraDep, `package.optBarrel, `package.optCache,
  `package.optRelease, `package.release, `package.transDeps]
-/
#guard_msgs in
#eval Lake.initPackageFacetConfigs.toList.map (·.1) |>.toArray |>.qsort (·.toString < ·.toString)
```
```lean -show
-- Always keep this in sync with the description below. It ensures that the list is complete.
/--
info: [`lean_lib.extraDep, `lean_lib.leanArts, `lean_lib.static.export, `lean_lib.shared, `lean_lib.modules, `lean_lib.static,
  `lean_lib.default]
-/
#guard_msgs in
#eval Lake.initLibraryFacetConfigs.toList.map (·.1)
```
```lean -show
-- Always keep this in sync with the description below. It ensures that the list is complete.
/--
info: module.bc
module.bc.o
module.c
module.c.o
module.c.o.export
module.c.o.noexport
module.deps
module.dynlib
module.exportInfo
module.header
module.ilean
module.importAllArts
module.importArts
module.importInfo
module.imports
module.input
module.ir
module.lean
module.leanArts
module.o
module.o.export
module.o.noexport
module.olean
module.olean.private
module.olean.server
module.precompileImports
module.setup
module.transImports
-/
#guard_msgs in
#eval Lake.initModuleFacetConfigs.toList.toArray.map (·.1) |>.qsort (·.toString < ·.toString) |>.forM (IO.println)
```
```lean -show
section
open Lake DSL
```
```lean
script "list-deps" := do
  let mut results := #[]
  for p in (← getWorkspace).packages do
    if p.name ≠ (← getWorkspace).root.name then
      results := results.push (p.name.toString, p.remoteUrl)
  results := results.qsort (·.1 < ·.1)
  IO.println "Dependencies:"
  for (name, url) in results do
    IO.println s!"{name}:\t{url}"
  return 0
```
```lean -show
end
```
```lean -show
section
open Lake
#synth MonadWorkspace ScriptM

end
``````lean -show
-- Test the claim above
/--
info: def Lake.envToBool? : String → Option Bool :=
fun o =>
  if ["y", "yes", "t", "true", "on", "1"].contains o.toLower = true then some true
  else if ["n", "no", "f", "false", "off", "0"].contains o.toLower = true then some false else none
-/
#guard_msgs in
#print Lake.envToBool?
``````lean -show
def main : List String → IO UInt32 := fun _ => pure 0
```
```lean -show
def main : List String → IO UInt32 := fun _ => pure 0
```
```lean -show
section
open Lake DSL
open Lean (NameMap)
```
```lean -show
section
example : Lake.Glob := `n

/-- info: instCoeNameGlob -/
#check_msgs in
#synth Coe Lean.Name Lake.Glob

open Lake DSL

/-- info: Lake.Glob.andSubmodules `n -/
#check_msgs in
#eval show Lake.Glob from `n.*

/-- info: Lake.Glob.submodules `n -/
#check_msgs in
#eval show Lake.Glob from `n.+

end
```
```lean -show
example : ScriptFn = (List String → ScriptM UInt32) := rfl
```