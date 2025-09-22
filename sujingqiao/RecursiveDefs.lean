```lean -show
section
variable (p : Nat → Bool)
```
```lean
def find (p : Nat → Bool) (i : Nat := 0) : Nat :=
  if p i then
    i
  else
    find p (i + 1)
partial_fixpoint
```
```lean -show
end
```
```lean -show
-- Test that nonempty is enough
inductive A : Type where
  | mkA
  | mkA'

instance : Nonempty A := ⟨.mkA⟩

def getA (n : Nat) : A :=
  getA (n + 1)
partial_fixpoint

example (n : Nat) : getA n = getA (n + 3) := by
  conv => lhs; rw [getA, getA, getA]
```
```lean
def loop (x : Nat) : Nat := loop (x + 1)
partial_fixpoint
```
```lean
def Array.find (xs : Array α) (p : α → Bool)
    (i : Nat := 0) : Option α :=
  if h : i < xs.size then
    if p xs[i] then
      some xs[i]
    else
      Array.find xs p (i + 1)
  else
    none
partial_fixpoint
```
```lean -keep +error (name := nonTailPos)
def List.findIndex (xs : List α) (p : α → Bool) : Int :=
  match xs with
  | [] => -1
  | x::ys =>
    if p x then
      0
    else
      have r := List.findIndex ys p
      if r = -1 then -1 else r + 1
partial_fixpoint
```
```leanOutput nonTailPos
Could not prove 'List.findIndex' to be monotone in its recursive calls:
  Cannot eliminate recursive call `List.findIndex ys p` enclosed in
    if ys✝.findIndex p = -1 then -1 else ys✝.findIndex p + 1
  Tried to apply 'monotone_ite', but failed.
  Possible cause: A missing `MonoBind` instance.
  Use `set_option trace.Elab.Tactic.monotonicity true` to debug.
```
```leanOutput nonTailPos
Could not prove 'List.findIndex' to be monotone in its recursive calls:
  Cannot eliminate recursive call `List.findIndex ys p` enclosed in
    if ys✝.findIndex p = -1 then -1 else ys✝.findIndex p + 1
  Tried to apply 'monotone_ite', but failed.
  Possible cause: A missing `MonoBind` instance.
  Use `set_option trace.Elab.Tactic.monotonicity true` to debug.
```
```lean -keep
def ack : (n m : Nat) → Option Nat
  | 0,   y   => some (y+1)
  | x+1, 0   => ack x 1
  | x+1, y+1 => do ack x (← ack (x+1) y)
partial_fixpoint
```
```lean -keep
structure Tree where cs : List Tree

def Tree.rev (t : Tree) : Option Tree := do
  Tree.mk (← t.cs.reverse.mapM (Tree.rev ·))
partial_fixpoint

def Tree.rev' (t : Tree) : Option Tree := do
  let mut cs := []
  for c in t.cs do
    cs := (← c.rev') :: cs
  return Tree.mk cs
partial_fixpoint
```
```lean -keep +error (name := monoMatch)
def List.findIndex (xs : List α) (p : α → Bool) : Option Nat :=
  match xs with
  | [] => none
  | x::ys =>
    if p x then
      some 0
    else
      match List.findIndex ys p with
      | none => none
      | some r => some (r + 1)
partial_fixpoint
```
```leanOutput monoMatch
Could not prove 'List.findIndex' to be monotone in its recursive calls:
  Cannot eliminate recursive call `List.findIndex ys p` enclosed in
    match ys✝.findIndex p with
    | none => none
    | some r => some (r + 1)
```
```leanOutput monoMatch
Could not prove 'List.findIndex' to be monotone in its recursive calls:
  Cannot eliminate recursive call `List.findIndex ys p` enclosed in
    match ys✝.findIndex p with
    | none => none
    | some r => some (r + 1)
```
```lean
def List.findIndex (xs : List α) (p : α → Bool) : Option Nat :=
  match xs with
  | [] => none
  | x::ys =>
    if p x then
      some 0
    else
      (· + 1) <$> List.findIndex ys p
partial_fixpoint
```
```lean
def List.findIndex (xs : List α) (p : α → Bool) : Option Nat :=
  match xs with
  | [] => none
  | x::ys =>
    if p x then
      some 0
    else
      (· + 1) <$> List.findIndex ys p
partial_fixpoint
```
```lean
theorem List.findIndex_implies_pred
    (xs : List α) (p : α → Bool) :
    xs.findIndex p = some i →
    ∃x, xs[i]? = some x ∧ p x := by
  apply List.findIndex.partial_correctness
          (motive := fun xs i => ∃ x, xs[i]? = some x ∧ p x)
  intro findIndex ih xs r hsome
  split at hsome
  next => contradiction
  next x ys =>
    split at hsome
    next =>
      have : r = 0 := by simp_all
      simp_all
    next =>
      simp only [Option.map_eq_map, Option.map_eq_some'] at hsome
      obtain ⟨r', hr, rfl⟩ := hsome
      specialize ih _ _ hr
      simpa
```
```lean -show
section
open Lean.Order
variable {α : Type u} {β : Type v} [PartialOrder α] [PartialOrder β] (f : α → β) (x y : α)
```
```lean -show
section
universe u v
variable (α : Type u)
variable (β : α → Sort v) [∀ x, CCPO (β x)]
variable (w : α)
```
```lean -show
end
```
```lean -show
section
set_option linter.unusedVariables false
variable {α : Sort u} {β : Sort v} [PartialOrder α] [PartialOrder β] (more : (x : α) → β) (x : α)

local macro "…" x:term:arg "…" : term => `(more $x)
```
```lean -show
end
``````lean -show
section
variable (n n' : Nat)
```
```lean
def countdown (n : Nat) : List Nat :=
  match n with
  | 0 => []
  | n' + 1 => n' :: countdown n'
```
```lean +error (name := countdown') -keep
def countdown' (n : Nat) : List Nat :=
  if n == 0 then []
  else
    let n' := n - 1
    n' :: countdown' n'
```
```leanOutput countdown'
fail to show termination for
  countdown'
with errors
failed to infer structural recursion:
Cannot use parameter n:
  failed to eliminate recursive application
    countdown' n'


failed to prove termination, possible solutions:
  - Use `have`-expressions to prove the remaining goals
  - Use `termination_by` to specify a different well-founded relation
  - Use `decreasing_by` to specify your own tactic for discharging this kind of goal
n : Nat
h✝ : ¬(n == 0) = true
n' : Nat := n - 1
⊢ n - 1 < n
```
```leanOutput countdown'
fail to show termination for
  countdown'
with errors
failed to infer structural recursion:
Cannot use parameter n:
  failed to eliminate recursive application
    countdown' n'


failed to prove termination, possible solutions:
  - Use `have`-expressions to prove the remaining goals
  - Use `termination_by` to specify a different well-founded relation
  - Use `decreasing_by` to specify your own tactic for discharging this kind of goal
n : Nat
h✝ : ¬(n == 0) = true
n' : Nat := n - 1
⊢ n - 1 < n
```
```lean
def countdown' (n : Nat) : List Nat :=
  if n = 0 then []
  else
    let n' := n - 1
    n' :: countdown' n'
```
```lean -show
end
```
```lean -keep
def half (n : Nat) : Nat :=
  match n with
  | 0 | 1 => 0
  | n + 2 => half n + 1
termination_by structural n
```
```lean -keep
def half : Nat → Nat
  | 0 | 1 => 0
  | n + 2 => half n + 1
termination_by structural n => n
```
```lean +error (name := badnoindct)
def notInductive (x : Nat → Nat) : Nat :=
  notInductive (fun n => x (n+1))
termination_by structural x
```
```leanOutput badnoindct
cannot use specified measure for structural recursion:
  its type is not an inductive
```
```leanOutput badnoindct
cannot use specified measure for structural recursion:
  its type is not an inductive
```
```lean +error (name := badidx)
inductive Fin' : Nat → Type where
  | zero : Fin' (n+1)
  | succ : Fin' n → Fin' (n+1)

def constantIndex (x : Fin' 100) : Nat := constantIndex .zero
termination_by structural x
```
```leanOutput badidx
cannot use specified measure for structural recursion:
  its type Fin' is an inductive family and indices are not variables
    Fin' 100
```
```leanOutput badidx
cannot use specified measure for structural recursion:
  its type Fin' is an inductive family and indices are not variables
    Fin' 100
```
```lean +error (name := badparam)
inductive WithParam' (p : Nat) : Nat → Type where
  | zero : WithParam' p (n+1)
  | succ : WithParam' p n → WithParam' p (n+1)

def afterVarying (n : Nat) (p : Nat) (x : WithParam' p n) : Nat :=
  afterVarying (n+1) p .zero
termination_by structural x
```
```leanOutput badparam
failed to infer structural recursion:
Cannot use parameter x:
  failed to eliminate recursive application
    afterVarying (n + 1) p WithParam'.zero
```
```leanOutput badparam
failed to infer structural recursion:
Cannot use parameter x:
  failed to eliminate recursive application
    afterVarying (n + 1) p WithParam'.zero
```
```lean -show
section
variable (n : Nat)
```
```lean
def fib : Nat → Nat
  | 0 | 1 => 1
  | .succ (.succ n) =>  fib n + fib (.succ n)
termination_by structural n => n
```
```lean -show
end
```
```lean -show
section
variable {α : Type u} (n n' : Nat) (xs : List α)
```
```lean +error -keep (name := badtarget)
def half (n : Nat) : Nat :=
  match Option.some n with
  | .some (n' + 2) => half n' + 1
  | _ => 0
termination_by structural n
```
```leanOutput badtarget
failed to infer structural recursion:
Cannot use parameter n:
  failed to eliminate recursive application
    half n'
```
```leanOutput badtarget
failed to infer structural recursion:
Cannot use parameter n:
  failed to eliminate recursive application
    half n'
```
```lean
def half (n : Nat) : Nat :=
  match h : Option.some n with
  | .some (n' + 2) => half n' + 1
  | _ => 0
termination_by n
decreasing_by simp_all; omega
```
```lean +error -keep
def listLen : List α → Nat
  | [] => 0
  | xs => listLen xs.tail + 1
termination_by structural xs => xs
```
```lean -show
end
```
```lean -keep
def min' (n k : Nat) : Nat :=
  match n, k with
  | 0, _ => 0
  | _, 0 => 0
  | n' + 1, k' + 1 => min' n' k' + 1
termination_by structural n
```
```lean +error (name := noMin)
def min' (n k : Nat) : Nat :=
  match (n, k) with
  | (0, _) => 0
  | (_, 0) => 0
  | (n' + 1, k' + 1) => min' n' k' + 1
termination_by structural n
```
```leanOutput noMin
failed to infer structural recursion:
Cannot use parameter n:
  failed to eliminate recursive application
    min' n' k'
```
```leanOutput noMin
failed to infer structural recursion:
Cannot use parameter n:
  failed to eliminate recursive application
    min' n' k'
```
```lean +error (name := minpair) -keep
def min' (nk : Nat × Nat) : Nat :=
  match nk with
  | (0, _) => 0
  | (_, 0) => 0
  | (n' + 1, k' + 1) => min' (n', k') + 1
termination_by structural nk
```
```leanOutput minpair
failed to infer structural recursion:
Cannot use parameter nk:
  the type Nat × Nat does not have a `.brecOn` recursor
```
```leanOutput minpair
failed to infer structural recursion:
Cannot use parameter nk:
  the type Nat × Nat does not have a `.brecOn` recursor
```
```lean
def min' (nk : Nat × Nat) : Nat :=
  match nk with
  | (0, _) => 0
  | (_, 0) => 0
  | (n' + 1, k' + 1) => min' (n', k') + 1
termination_by nk
```
```lean -show
section
variable (n n' : Nat)
```
```lean
def countdown (n : Nat) : List Nat :=
  match n with
  | 0 => []
  | n' + 1 => n' :: countdown (n' + 0)
termination_by structural n
```
```lean +error (name := countdownNonDefEq)
def countdown' (n : Nat) : List Nat :=
  match n with
  | 0 => []
  | n' + 1 => n' :: countdown' (0 + n')
termination_by structural n
```
```leanOutput countdownNonDefEq
failed to infer structural recursion:
Cannot use parameter n:
  failed to eliminate recursive application
    countdown' (0 + n')
```
```leanOutput countdownNonDefEq
failed to infer structural recursion:
Cannot use parameter n:
  failed to eliminate recursive application
    countdown' (0 + n')
```
```lean -show
end
```
```lean
mutual
  def even : Nat → Prop
    | 0 => True
    | n+1 => odd n
  termination_by structural n => n

  def odd : Nat → Prop
    | 0 => False
    | n+1 => even n
  termination_by structural n => n
end
```
```lean
mutual
  inductive Exp where
    | var : String → Exp
    | app : App → Exp

  inductive App where
    | fn : String → App
    | app : App → Exp → App
end

mutual
  def Exp.size : Exp → Nat
    | .var _ => 1
    | .app a => a.size
  termination_by structural e => e

  def App.size : App → Nat
    | .fn _ => 1
    | .app a e => a.size + e.size + 1
  termination_by structural a => a
end
```
```lean
def App.numArgs : App → Nat
  | .fn _ => 0
  | .app a _ => a.numArgs + 1
termination_by structural a => a
```
```lean (name := inferStruct)
def half : Nat → Nat
  | 0 | 1 => 0
  | n + 2 => half n + 1
termination_by?
```
```leanOutput inferStruct
Try this:
  termination_by structural x => x
```
```leanOutput inferStruct
Try this:
  termination_by structural x => x
```
```lean -show
section
```
```lean -keep
def half : Nat → Nat
  | 0 | 1 => 0
  | n + 2 => half n + 1
```
```lean -keep
def half : Nat → Nat
  | .zero | .succ .zero => .zero
  | .succ (.succ n) => half n |>.succ
```
```lean -keep -show
-- Test of next block - visually check correspondence when updating!
set_option trace.Elab.definition.body true in
set_option pp.all true in

/--
trace: [Elab.definition.body] half : Nat → Nat :=
    fun (x : Nat) =>
      half.match_1.{1} (fun (x : Nat) => Nat) x (fun (_ : Unit) => Nat.zero) (fun (_ : Unit) => Nat.zero)
        fun (n : Nat) => Nat.succ (_root_.half n)
-/
#guard_msgs in
def half : Nat → Nat
  | .zero | .succ .zero => .zero
  | .succ (.succ n) => half n |>.succ
```
```lean (name := tracedHalf)
set_option trace.Elab.definition.body true in
set_option pp.all true in

def half : Nat → Nat
  | .zero | .succ .zero => .zero
  | .succ (.succ n) => half n |>.succ
```
```lean (name := halfmatch)
#print half.match_1
```
```leanOutput halfmatch (whitespace := lax)
def half.match_1.{u_1} :
    (motive : Nat → Sort u_1) → (x : Nat) →
    (Unit → motive Nat.zero) → (Unit → motive 1) →
    ((n : Nat) → motive n.succ.succ) →
    motive x :=
  fun motive x h_1 h_2 h_3 =>
    Nat.casesOn x (h_1 ()) fun n =>
      Nat.casesOn n (h_2 ()) fun n =>
        h_3 n
```
```leanOutput halfmatch (whitespace := lax)
def half.match_1.{u_1} :
    (motive : Nat → Sort u_1) → (x : Nat) →
    (Unit → motive Nat.zero) → (Unit → motive 1) →
    ((n : Nat) → motive n.succ.succ) →
    motive x :=
  fun motive x h_1 h_2 h_3 =>
    Nat.casesOn x (h_1 ()) fun n =>
      Nat.casesOn n (h_2 ()) fun n =>
        h_3 n
```
```lean
def half.match_1'.{u} :
    (motive : Nat → Sort u) → (x : Nat) →
    (Unit → motive Nat.zero) → (Unit → motive 1) →
    ((n : Nat) → motive n.succ.succ) →
    motive x :=
  fun motive x h_1 h_2 h_3 =>
    Nat.casesOn x (h_1 ()) fun n =>
      Nat.casesOn n (h_2 ()) fun n =>
        h_3 n
```
```lean
def half' : Nat → Nat :=
  fun (x : Nat) =>
    half.match_1 (motive := fun _ => Nat) x
      (fun _ => 0) -- Case for 0
      (fun _ => 0) -- Case for 1
      (fun n => Nat.succ (half' n)) -- Case for n + 2
```
```lean +error -keep
noncomputable
def half'' : Nat → Nat :=
  fun (x : Nat) =>
    x.brecOn fun n table =>
      _
/- To translate:
    half.match_1 (motive := fun _ => Nat) x
      (fun _ => 0) -- Case for 0
      (fun _ => 0) -- Case for 1
      (fun n => Nat.succ (half' n)) -- Case for n + 2
-/
```
```lean +error -keep (name := threeCases)
noncomputable
def half'' : Nat → Nat :=
  fun (x : Nat) =>
    x.brecOn fun n table =>
      (half.match_1
        (motive :=
          fun k =>
            k.below (motive := fun _ => Nat) →
            Nat)
        n
        _
        _
        _)
      table
/- To translate:
      (fun _ => 0) -- Case for 0
      (fun _ => 0) -- Case for 1
      (fun n => Nat.succ (half' n)) -- Case for n + 2
-/
```
```leanOutput threeCases
don't know how to synthesize placeholder for argument `h_1`
context:
x n : Nat
table : Nat.below n
⊢ Unit → (fun k => Nat.below k → Nat) Nat.zero
```
```leanOutput threeCases
don't know how to synthesize placeholder for argument `h_1`
context:
x n : Nat
table : Nat.below n
⊢ Unit → (fun k => Nat.below k → Nat) Nat.zero
```
```leanOutput threeCases
don't know how to synthesize placeholder for argument `h_2`
context:
x n : Nat
table : Nat.below n
⊢ Unit → (fun k => Nat.below k → Nat) 1
```
```leanOutput threeCases
don't know how to synthesize placeholder for argument `h_2`
context:
x n : Nat
table : Nat.below n
⊢ Unit → (fun k => Nat.below k → Nat) 1
```
```leanOutput threeCases
don't know how to synthesize placeholder for argument `h_3`
context:
x n : Nat
table : Nat.below n
⊢ (n : Nat) → (fun k => Nat.below k → Nat) n.succ.succ
```
```leanOutput threeCases
don't know how to synthesize placeholder for argument `h_3`
context:
x n : Nat
table : Nat.below n
⊢ (n : Nat) → (fun k => Nat.below k → Nat) n.succ.succ
```
```lean +error -keep (name := oneMore)
noncomputable
def half'' : Nat → Nat :=
  fun (x : Nat) =>
    x.brecOn fun n table =>
      (half.match_1
        (motive :=
          fun k =>
            k.below (motive := fun _ => Nat) →
            Nat)
        n
        (fun () _ => .zero)
        (fun () _ => .zero)
        _)
      table
/- To translate:
      (fun n => Nat.succ (half' n)) -- Case for n + 2
-/
```
```leanTerm
(n : Nat) →
Nat.below (motive := fun _ => Nat) n.succ.succ →
Nat
```
```leanTerm
(n : Nat) →
Nat ×' (Nat ×' Nat.below (motive := fun _ => Nat) n) →
Nat
```
```lean -show
example : ((n : Nat) →
Nat.below (motive := fun _ => Nat) n.succ.succ →
Nat) = ((n : Nat) →
Nat ×' (Nat ×' Nat.below (motive := fun _ => Nat) n) →
Nat) := rfl
```
```lean -show

variable {n : Nat}
```
```lean +error -keep (name := oneMore)
noncomputable
def half'' : Nat → Nat :=
  fun (x : Nat) =>
    x.brecOn fun n table =>
      (half.match_1
        (motive :=
          fun k =>
            k.below (motive := fun _ => Nat) →
            Nat)
        n
        (fun () _ => .zero)
        (fun () _ => .zero)
        (fun _ table => Nat.succ table.2.1)
      table
```
```lean -show
end
``````lean
def div (n k : Nat) : Nat :=
  if k = 0 then 0
  else if k > n then 0
  else 1 + div (n - k) k
termination_by n
```
```lean -show
section
variable {α : Type u} {β : Type v} (a₁ a₂ : α) (b₁ b₂ : β) [WellFoundedRelation α] [WellFoundedRelation β]
variable {γ : Type u} (x₁ x₂ : γ) [SizeOf γ]
local notation x " ≺ " y => WellFoundedRelation.rel x y
```
```lean -show
end
```
```lean -show

-- Check claims about instSizeOfDefault

example {α} (x : α) : sizeOf x = 0 := by rfl

/-- info: instSizeOfDefault.{u} (α : Sort u) : SizeOf α -/
#check_msgs in
#check instSizeOfDefault

```
```lean -keep
def fooInst (b : Bool → Bool) : Unit := fooInst (b ∘ b)
termination_by b
decreasing_by
  guard_target =
    @sizeOf (Bool → Bool) (instSizeOfDefault _) (b ∘ b) < sizeOf b
  simp only [sizeOf, default.sizeOf]
  guard_target = 0 < 0
  simp
  guard_target = False
  sorry
```
```lean -show
section
variable {α : Type u} {β : α → Type v} {β' : Type v} (more : β') (g : (x : α) → (y : β x) → β' → γ) [WellFoundedRelation γ] (a₁ p₁ : α) (a₂ : β a₁) (p₂ : β p₁)

local notation (name := decRelStx) x " ≺ " y => WellFoundedRelation.rel x y
local notation "…" => more

```
```lean -show
end
```
```lean -show
section
variable {n : Nat}
```
```lean +error -keep (name := fibGoals)
def fib (n : Nat) :=
  if h : n ≤ 1 then
    1
  else
    fib (n - 1) + fib (n - 2)
termination_by n
decreasing_by
  skip
```
```leanOutput fibGoals (whitespace := lax) -show
unsolved goals
   n : Nat
   h : ¬n ≤ 1
   ⊢ n - 1 < n

   n : Nat
   h : ¬n ≤ 1
   ⊢ n - 2 < n
```
```leanOutput fibGoals (whitespace := lax) -show
unsolved goals
   n : Nat
   h : ¬n ≤ 1
   ⊢ n - 1 < n

   n : Nat
   h : ¬n ≤ 1
   ⊢ n - 2 < n
```
```lean -keep
def fib (n : Nat) :=
  if h : n ≤ 1 then
    1
  else
    fib (n - 1) + fib (n - 2)
termination_by n
decreasing_by
  · omega
  · omega
```
```lean -show
end
```
```lean +error -keep (name := fibGoals2)
def fib : Nat → Nat
  | 0 | 1 => 1
  | .succ (.succ n) => fib (n + 1) + fib n
termination_by n => n
decreasing_by
  skip
```
```leanOutput fibGoals2 (whitespace := lax) -show
unsolved goals
n : Nat
⊢ n + 1 < n.succ.succ

n : Nat
⊢ n < n.succ.succ
```
```leanOutput fibGoals2 (whitespace := lax) -show
unsolved goals
n : Nat
⊢ n + 1 < n.succ.succ

n : Nat
⊢ n < n.succ.succ
```
```lean -show
section
variable {x : Nat} {xs : List Nat} {n : Nat}
```
```lean +error -keep (name := fibGoals3)
def fib (n : Nat) :=
  if n ≤ 1 then
    1
  else
    fib (n - 1) + fib (n - 2)
termination_by n
decreasing_by
  skip
```
```leanOutput fibGoals3 (whitespace := lax) -show
unsolved goals
   n : Nat
   h✝ : ¬n ≤ 1
   ⊢ n - 1 < n

   n : Nat
   h✝ : ¬n ≤ 1
   ⊢ n - 2 < n
```
```leanOutput fibGoals3 (whitespace := lax) -show
unsolved goals
   n : Nat
   h✝ : ¬n ≤ 1
   ⊢ n - 1 < n

   n : Nat
   h✝ : ¬n ≤ 1
   ⊢ n - 2 < n
```
```lean +error -keep (name := nestGoal3)
def f (xs : Array Nat) : Nat := Id.run do
  let mut s := xs.sum
  for i in [:xs.size] do
    s := s + f (xs.take i)
  pure s
termination_by xs
decreasing_by
  skip
```
```leanOutput nestGoal3 (whitespace := lax) -show
unsolved goals
xs : Array Nat
i : Nat
h✝ : i ∈ [:xs.size]
⊢ sizeOf (xs.take i) < sizeOf xs
```
```leanOutput nestGoal3 (whitespace := lax) -show
unsolved goals
xs : Array Nat
i : Nat
h✝ : i ∈ [:xs.size]
⊢ sizeOf (xs.take i) < sizeOf xs
```
```lean +error -keep (name := nestGoal1)
def f (n : Nat) (xs : List Nat) : Nat :=
  List.sum (xs.map (fun x => f x []))
termination_by xs
decreasing_by
  skip
```
```leanOutput nestGoal1 (whitespace := lax) -show
unsolved goals
n : Nat
xs : List Nat
x : Nat
h✝ : x ∈ xs
⊢ sizeOf [] < sizeOf xs
```
```leanOutput nestGoal1 (whitespace := lax) -show
unsolved goals
n : Nat
xs : List Nat
x : Nat
h✝ : x ∈ xs
⊢ sizeOf [] < sizeOf xs
```
```lean +error -keep (name := nestGoal4)
def List.myMap := @List.map
def f (n : Nat) (xs : List Nat) : Nat :=
  List.sum (xs.myMap (fun x => f x []))
termination_by xs
decreasing_by
  skip
```
```leanOutput nestGoal4 (whitespace := lax) -show
unsolved goals
n : Nat
xs : List Nat
x : Nat
⊢ sizeOf [] < sizeOf xs
```
```leanOutput nestGoal4 (whitespace := lax) -show
unsolved goals
n : Nat
xs : List Nat
x : Nat
⊢ sizeOf [] < sizeOf xs
```
```lean -show
end
```
```lean -show
section
```
```lean -keep
def ack : Nat → Nat → Nat
  | 0,     n     => n + 1
  | m + 1, 0     => ack m 1
  | m + 1, n + 1 => ack m (ack (m + 1) n)
termination_by m n => (m, n)
```
```lean -keep +error (name := synack)
def synack : Nat → Nat → Nat
  | 0,     n     => n + 1
  | m + 1, 0     => synack m 1
  | m + 1, n + 1 => synack m (synack (m / 2 + 1) n)
termination_by m n => (m, n)
```
```leanOutput synack (whitespace := lax)
failed to prove termination, possible solutions:
  - Use `have`-expressions to prove the remaining goals
  - Use `termination_by` to specify a different well-founded relation
  - Use `decreasing_by` to specify your own tactic for discharging this kind of goal
case h
m n : Nat
⊢ m / 2 + 1 < m + 1
```
```leanOutput synack (whitespace := lax)
failed to prove termination, possible solutions:
  - Use `have`-expressions to prove the remaining goals
  - Use `termination_by` to specify a different well-founded relation
  - Use `decreasing_by` to specify your own tactic for discharging this kind of goal
case h
m n : Nat
⊢ m / 2 + 1 < m + 1
```
```lean -keep
def synack : Nat → Nat → Nat
  | 0, n => n + 1
  | m + 1, 0 => synack m 1
  | m + 1, n + 1 => synack m (synack (m / 2 + 1) n)
termination_by m n => (m, n)
decreasing_by
  · apply Prod.Lex.left
    omega
  -- the next goal corresponds to the third recursive call
  · apply Prod.Lex.right'
    · omega
    · omega
  · apply Prod.Lex.left
    omega
```
```lean -show
section
variable {e₁ e₂ i j : Nat}
```
```lean (name := binarySearch)
def binarySearch (x : Int) (xs : Array Int) : Option Nat :=
  go 0 xs.size
where
  go (i j : Nat) (hj : j ≤ xs.size := by omega) :=
    if h : i < j then
      let mid := (i + j) / 2
      let y := xs[mid]
      if x = y then
        some mid
      else if x < y then
        go i mid
      else
        go (mid + 1) j
    else
      none
  termination_by?
```
```leanOutput binarySearch
Try this:
  termination_by (j, j - i)
```
```leanOutput binarySearch
Try this:
  termination_by (j, j - i)
```
```lean -show
end
```
```lean -keep +error
def ack : Nat → Nat → Nat
  | 0, n => n + 1
  | m + 1, 0 => ack m 1
  | m + 1, n + 1 => ack m (ack (m + 1) n)
decreasing_by
  · apply Prod.Lex.left
    omega
  · apply Prod.Lex.right
    omega
  · apply Prod.Lex.left
    omega
```
```lean +error (name := badInfer)
def notAck : Nat → Nat → Nat
  | 0, n => n + 1
  | m + 1, 0 => notAck m 1
  | m + 1, n + 1 => notAck m (notAck (m / 2 + 1) n)
decreasing_by all_goals decreasing_tactic
```
```leanOutput badInfer
failed to prove termination, possible solutions:
  - Use `have`-expressions to prove the remaining goals
  - Use `termination_by` to specify a different well-founded relation
  - Use `decreasing_by` to specify your own tactic for discharging this kind of goal
case h
m n : Nat
⊢ m / 2 + 1 < m + 1
```
```leanOutput badInfer
failed to prove termination, possible solutions:
  - Use `have`-expressions to prove the remaining goals
  - Use `termination_by` to specify a different well-founded relation
  - Use `decreasing_by` to specify your own tactic for discharging this kind of goal
case h
m n : Nat
⊢ m / 2 + 1 < m + 1
```
```lean (name := fg)
mutual
  def f : (n : Nat) → Nat
    | 0 => 0
    | n+1 => g n
  termination_by?

  def g (n : Nat) : Nat := (f n) + 1
  termination_by?
end
```
```leanOutput fg
Try this:
  termination_by (n, 1)
```
```leanOutput fg
Try this:
  termination_by (n, 1)
```
```leanOutput fg
Try this:
  termination_by (n, 1)
```
```leanOutput fg
Try this:
  termination_by (n, 1)
```
```lean -show
section
variable (xs : List α) (p : α → Bool) (f : α → β) (x : α)
```
```lean -show
end
```
```lean -show
section
variable {α : Type u}
```
```lean
noncomputable def div (n k : Nat) : Nat :=
  (inferInstanceAs (WellFoundedRelation Nat)).wf.fix
    (fun n r =>
      if h : k = 0 then 0
      else if h : k > n then 0
      else 1 + (r (n - k) <| by
        show (n - k) < n
        omega))
    n
```
```lean +error (name := nonDef) -keep
theorem div.eq0 : div n 0 = 0 := by rfl
```
```leanOutput nonDef
Tactic `rfl` failed: The left-hand side
  div n 0
is not definitionally equal to the right-hand side
  0

n : Nat
⊢ div n 0 = 0
```
```leanOutput nonDef
Tactic `rfl` failed: The left-hand side
  div n 0
is not definitionally equal to the right-hand side
  0

n : Nat
⊢ div n 0 = 0
```
```lean
theorem div.eq0 : div n 0 = 0 := by
  unfold div
  apply WellFounded.fix_eq

theorem div.eq1 : k > n → div n k = 0 := by
  intro h
  unfold div
  rw [WellFounded.fix_eq]
  simp only [gt_iff_lt, dite_eq_ite, ite_eq_left_iff, Nat.not_lt]
  intros; omega

theorem div.eq2 :
    ¬ k = 0 → ¬ (k > n) →
    div n k = 1 + div (n - k) k := by
  intros
  unfold div
  rw [WellFounded.fix_eq]
  simp_all only [
    gt_iff_lt, Nat.not_lt,
    dite_false, dite_eq_ite,
    ite_false, ite_eq_right_iff
  ]
  omega
``````lean +error -keep (name := badwf)
def f : (n m l : Nat) → Nat
  | n+1, m+1, l+1 => [
      f (n+1) (m+1) (l+1),
      f (n+1) (m-1) (l),
      f (n)   (m+1) (l) ].sum
  | _, _, _ => 0
decreasing_by all_goals decreasing_tactic
```
```leanOutput badwf (whitespace := lax)
Could not find a decreasing measure.
The basic measures relate at each recursive call as follows:
(<, ≤, =: relation proved, ? all proofs failed, _: no proof attempted)
           n m l
1) 32:6-25 = = =
2) 33:6-23 = < _
3) 34:6-23 < _ _
Please use `termination_by` to specify a decreasing measure.
```
```leanOutput badwf (whitespace := lax)
Could not find a decreasing measure.
The basic measures relate at each recursive call as follows:
(<, ≤, =: relation proved, ? all proofs failed, _: no proof attempted)
           n m l
1) 32:6-25 = = =
2) 33:6-23 = < _
3) 34:6-23 < _ _
Please use `termination_by` to specify a decreasing measure.
``````lean
/-- A homogeneous pair -/
structure Pair (α : Type u) where
  fst : α
  snd : α

/-- Mapping a function over the elements of a pair -/
def Pair.map (f : α → β) (p : Pair α) : Pair β where
  fst := f p.fst
  snd := f p.snd
```
```lean
/-- A binary tree defined using `Pair` -/
inductive Tree (α : Type u) where
  | leaf : α → Tree α
  | node : Pair (Tree α) → Tree α
```
```lean +error -keep (name := badwf)
def Tree.map (f : α → β) : Tree α → Tree β
  | leaf x => leaf (f x)
  | node p => node (p.map (fun t' => t'.map f))
termination_by t => t
```
```leanOutput badwf (whitespace := lax)
failed to prove termination, possible solutions:
  - Use `have`-expressions to prove the remaining goals
  - Use `termination_by` to specify a different well-founded relation
  - Use `decreasing_by` to specify your own tactic for discharging this kind of goal
α : Type u_1
p : Pair (Tree α)
t' : Tree α
⊢ sizeOf t' < 1 + sizeOf p
```
```leanOutput badwf (whitespace := lax)
failed to prove termination, possible solutions:
  - Use `have`-expressions to prove the remaining goals
  - Use `termination_by` to specify a different well-founded relation
  - Use `decreasing_by` to specify your own tactic for discharging this kind of goal
α : Type u_1
p : Pair (Tree α)
t' : Tree α
⊢ sizeOf t' < 1 + sizeOf p
```
```lean -show
section
variable (t' : Tree α) (p : Pair (Tree α))
```
```lean -show
end
```
```lean
inductive Pair.Mem (p : Pair α) : α → Prop where
  | fst : Mem p p.fst
  | snd : Mem p p.snd

instance : Membership α (Pair α) where
  mem := Pair.Mem
```
```lean
theorem Pair.sizeOf_lt_of_mem {α} [SizeOf α]
    {p : Pair α} {x : α} (h : x ∈ p) :
    sizeOf x < sizeOf p := by
  cases h <;> cases p <;> (simp; omega)
```
```lean
def Pair.attach (p : Pair α) : Pair {x : α // x ∈ p} where
  fst := ⟨p.fst, .fst⟩
  snd := ⟨p.snd, .snd⟩

def Pair.unattach {P : α → Prop} :
    Pair {x : α // P x} → Pair α :=
  Pair.map Subtype.val
```
```lean -keep
def Tree.map (f : α → β) : Tree α → Tree β
  | leaf x => leaf (f x)
  | node p => node (p.attach.map (fun ⟨t', _⟩ => t'.map f))
termination_by t => t
decreasing_by
  have := Pair.sizeOf_lt_of_mem ‹_›
  simp_all +arith
  omega
```
```lean
@[wf_preprocess]
theorem Pair.map_wfParam (f : α → β) (p : Pair α) :
    (wfParam p).map f = p.attach.unattach.map f := by
  cases p
  simp [wfParam, Pair.attach, Pair.unattach, Pair.map]

@[wf_preprocess]
theorem Pair.map_unattach {P : α → Prop}
    (p : Pair (Subtype P)) (f : α → β) :
    p.unattach.map f =
    p.map fun ⟨x, h⟩ =>
      binderNameHint x f <|
      f (wfParam x) := by
  cases p; simp [wfParam, Pair.unattach, Pair.map]
```
```lean -keep
def Tree.map (f : α → β) : Tree α → Tree β
  | leaf x => leaf (f x)
  | node p => node (p.map (fun t' => t'.map f))
termination_by t => t
decreasing_by
  have := Pair.sizeOf_lt_of_mem ‹_›
  simp_all
  omega
```
```lean
macro "sizeOf_pair_dec" : tactic =>
  `(tactic| with_reducible
    have := Pair.sizeOf_lt_of_mem ‹_›
    omega
    done)

macro_rules
  | `(tactic| decreasing_trivial) =>
    `(tactic| sizeOf_pair_dec)

def Tree.map (f : α → β) : Tree α → Tree β
  | leaf x => leaf (f x)
  | node p => node (p.map (fun t' => t'.map f))
termination_by t => t
``````lean
def List.below' {α : Type u} {motive : List α → Sort u} :
    List α → Sort (max (u + 1) u)
  | [] => PUnit
  | _ :: xs => motive xs ×' xs.below' (motive := motive)
```
```lean -show
theorem List.below_eq_below' : @List.below = @List.below' := by
  funext α motive xs
  induction xs <;> simp [below']
  congr
```
```lean
inductive Tree (α : Type u) : Type u where
  | leaf
  | branch (left : Tree α) (val : α) (right : Tree α)
```
```lean
def Tree.below' {α : Type u} {motive : Tree α → Sort u} :
    Tree α → Sort (max (u + 1) u)
  | .leaf => PUnit
  | .branch left _val right =>
    (motive left ×' left.below' (motive := motive)) ×'
    (motive right ×' right.below' (motive := motive))
```
```lean -show
theorem Tree.below_eq_below' : @Tree.below = @Tree.below' := by
  funext α motive t
  induction t
  next =>
    simp [Tree.below']
  next ihl ihr =>
    simp [Tree.below', ihl, ihr]

```
```lean
def List.brecOnTable {α : Type u}
    {motive : List α → Sort u}
    (xs : List α)
    (step :
      (ys : List α) →
      ys.below' (motive := motive) →
      motive ys) :
    motive xs ×' xs.below' (motive := motive) :=
  match xs with
  | [] => ⟨step [] PUnit.unit, PUnit.unit⟩
  | x :: xs =>
    let res := xs.brecOnTable (motive := motive) step
    let val := step (x :: xs) res
    ⟨val, res⟩
```
```lean
def Tree.brecOnTable {α : Type u}
    {motive : Tree α → Sort u}
    (t : Tree α)
    (step :
      (ys : Tree α) →
      ys.below' (motive := motive) →
      motive ys) :
    motive t ×' t.below' (motive := motive) :=
  match t with
  | .leaf => ⟨step .leaf PUnit.unit, PUnit.unit⟩
  | .branch left val right =>
    let resLeft := left.brecOnTable (motive := motive) step
    let resRight := right.brecOnTable (motive := motive) step
    let branchRes := ⟨resLeft, resRight⟩
    let val := step (.branch left val right) branchRes
    ⟨val, branchRes⟩
```
```lean
def List.brecOn' {α : Type u}
    {motive : List α → Sort u}
    (xs : List α)
    (step :
      (ys : List α) →
      ys.below' (motive := motive) →
      motive ys) :
    motive xs :=
  (xs.brecOnTable (motive := motive) step).1
```
```lean
def Tree.brecOn' {α : Type u}
    {motive : Tree α → Sort u}
    (t : Tree α)
    (step :
      (ys : Tree α) →
      ys.below' (motive := motive) →
      motive ys) :
    motive t :=
  (t.brecOnTable (motive := motive) step).1
```
```lean -show
-- Proving the above-claimed equivalence is too time consuming, but evaluating a few examples will at least catch silly mistakes!

/--
info: fun motive x y z step =>
  step [x, y, z]
    ⟨step [y, z] ⟨step [z] ⟨step [] PUnit.unit, PUnit.unit⟩, step [] PUnit.unit, PUnit.unit⟩,
      step [z] ⟨step [] PUnit.unit, PUnit.unit⟩, step [] PUnit.unit, PUnit.unit⟩
-/
#check_msgs in
#reduce fun motive x y z step => List.brecOn' (motive := motive) [x, y, z] step

/--
info: fun motive x y z step =>
  step [x, y, z]
    ⟨step [y, z] ⟨step [z] ⟨step [] PUnit.unit, PUnit.unit⟩, step [] PUnit.unit, PUnit.unit⟩,
      step [z] ⟨step [] PUnit.unit, PUnit.unit⟩, step [] PUnit.unit, PUnit.unit⟩
-/
#check_msgs in
#reduce fun motive x y z step => List.brecOn (motive := motive) [x, y, z] step

/--
info: fun motive x z step =>
  step ((Tree.leaf.branch x Tree.leaf).branch z Tree.leaf)
    ⟨⟨step (Tree.leaf.branch x Tree.leaf)
          ⟨⟨step Tree.leaf PUnit.unit, PUnit.unit⟩, step Tree.leaf PUnit.unit, PUnit.unit⟩,
        ⟨step Tree.leaf PUnit.unit, PUnit.unit⟩, step Tree.leaf PUnit.unit, PUnit.unit⟩,
      step Tree.leaf PUnit.unit, PUnit.unit⟩
-/
#check_msgs in
#reduce fun motive x z step => Tree.brecOn' (motive := motive) (.branch (.branch .leaf x .leaf) z .leaf) step

/--
info: fun motive x z step =>
  step ((Tree.leaf.branch x Tree.leaf).branch z Tree.leaf)
    ⟨⟨step (Tree.leaf.branch x Tree.leaf)
          ⟨⟨step Tree.leaf PUnit.unit, PUnit.unit⟩, step Tree.leaf PUnit.unit, PUnit.unit⟩,
        ⟨step Tree.leaf PUnit.unit, PUnit.unit⟩, step Tree.leaf PUnit.unit, PUnit.unit⟩,
      step Tree.leaf PUnit.unit, PUnit.unit⟩
-/
#check_msgs in
#reduce fun motive x z step => Tree.brecOn (motive := motive) (.branch (.branch .leaf x .leaf) z .leaf) step
``````lean -show
section
variable (n k : Nat) (mot : Nat → Sort u)
```
```lean
def add (n : Nat) : Nat → Nat
  | .zero => n
  | .succ k => .succ (add n k)
```
```lean
def add' (n : Nat) :=
  Nat.rec (motive := fun _ => Nat)
    n
    (fun k soFar => .succ soFar)
```
```lean
def half : Nat → Nat
  | 0 | 1 => 0
  | n + 2 => half n + 1
```
```lean
def helper : Nat → Bool → Nat :=
  Nat.rec (motive := fun _ => Bool → Nat)
    (fun _ => 0)
    (fun _ soFar =>
      fun b =>
        (if b then Nat.succ else id) (soFar !b))

def half' (n : Nat) : Nat := helper n false
```
```lean (name := halfTest)
#eval [0, 1, 2, 3, 4, 5, 6, 7, 8].map half'
```
```leanOutput halfTest
[0, 0, 1, 1, 2, 2, 3, 3, 4]
```
```leanOutput halfTest
[0, 0, 1, 1, 2, 2, 3, 3, 4]
```
```lean
noncomputable def half'' (n : Nat) : Nat :=
  Nat.brecOn n (motive := fun _ => Nat)
    fun k soFar =>
      match k, soFar with
      | 0, _ | 1, _ => 0
      | _ + 2, ⟨_, ⟨h, _⟩⟩ => h + 1
```
```lean (name := halfTest2)
#reduce [0,1,2,3,4,5,6,7,8].map half''
```
```leanOutput halfTest2
[0, 0, 1, 1, 2, 2, 3, 3, 4]
```
```leanOutput halfTest2
[0, 0, 1, 1, 2, 2, 3, 3, 4]
```
```lean
noncomputable def half''' (n : Nat) : Nat :=
  n.brecOn (motive := fun _ => Nat)
    fun k =>
      k.casesOn
        (motive :=
          fun k' =>
            (k'.below (motive := fun _ => Nat)) →
            Nat)
        (fun _ => 0)
        (fun k' =>
          k'.casesOn
            (motive :=
              fun k'' =>
                (k''.succ.below (motive := fun _ => Nat)) →
                Nat)
            (fun _ => 0)
            (fun _ soFar => soFar.2.1.succ))
```
```lean (name := halfTest3)
#reduce [0,1,2,3,4,5,6,7,8].map half''
```
```leanOutput halfTest3
[0, 0, 1, 1, 2, 2, 3, 3, 4]
```
```leanOutput halfTest3
[0, 0, 1, 1, 2, 2, 3, 3, 4]
```
```lean -show
end
```