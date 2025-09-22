```lean
open Lean Grind
```
```lean
example [CommRing α] (x : α) : (x + 1) * (x - 1) = x ^ 2 - 1 := by
  grind
```
```lean
example [CommRing α] [IsCharP α 256] (x : α) :
    (x + 16)*(x - 16) = x^2 := by
  grind
```
```lean
example (x : UInt8) : (x + 16) * (x - 16) = x ^ 2 := by
  grind
```
```lean
example [CommRing α] (a b c : α) :
    a + b + c = 3 →
    a ^ 2 + b ^ 2 + c ^ 2 = 5 →
    a ^ 3 + b ^ 3 + c ^ 3 = 7 →
    a ^ 4 + b ^ 4 = 9 - c ^ 4 := by
  grind
```
```lean
example [CommRing α] (x y : α) :
    x ^ 2 * y = 1 →
    x * y ^ 2 = y →
    y * x = 1 := by
  grind
```
```lean
example [CommRing α] [IsCharP α 0] (a : α) :
    a + 1 = 2 + a → False := by
  grind
```
```lean
example [CommRing α] (a b c : α)
    (h₁ : a + 6 = a) (h₂ : c = c + 9) (h : b + 3*c = 0) :
    27*a + b = 0 := by
  grind
```
```lean -show
variable {a b p : α} [Field α]
```
```lean
example [Field α] (a : α) :
    a ^ 2 = 0 →
    a = 0 := by
  grind
```
```lean
example [CommRing α] [NoNatZeroDivisors α] (a b : α) :
    2 * a + 2 * b = 0 →
    b ≠ -a → False := by
  grind
```
```lean (name := NoNatZero) +error
example [CommRing α] (a b : α) :
    2 * a + 2 * b = 0 →
    b ≠ -a → False := by
  grind
```
```leanOutput NoNatZero
`grind` failed
case grind
α : Type u_1
inst : CommRing α
a b : α
h : 2 * a + 2 * b = 0
h_1 : ¬b = -a
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] False propositions
  [eqc] Equivalence classes
  [ring] Ring `α`
```
```leanOutput NoNatZero
`grind` failed
case grind
α : Type u_1
inst : CommRing α
a b : α
h : 2 * a + 2 * b = 0
h_1 : ¬b = -a
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] False propositions
  [eqc] Equivalence classes
  [ring] Ring `α`
```
```lean
example [Field α] [NoNatZeroDivisors α] (a : α) :
    1 / a + 1 / (2 * a) = 3 / (2 * a) := by
  grind
```
```lean
example [Field α] (a : α) : (2 * a)⁻¹ = a⁻¹ / 2 := by grind
```
```lean
example [Field α] {x y z w : α} :
    x / y = z / w →
    y ≠ 0 → w ≠ 0 →
    x * w = z * y := by
  grind (splits := 0)
```
```lean +error (name := noRing)
example [CommRing α] (x y : α) :
    x ^ 2 * y = 1 →
    x * y ^ 2 = y →
    y * x = 1 := by
  grind -ring
```
```leanOutput noRing
`grind` failed
case grind
α : Type u_1
inst : CommRing α
x y : α
h : x ^ 2 * y = 1
h_1 : x * y ^ 2 = y
h_2 : ¬y * x = 1
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] False propositions
  [eqc] Equivalence classes
  [linarith] Linarith assignment for `α`
```
```leanOutput noRing
`grind` failed
case grind
α : Type u_1
inst : CommRing α
x y : α
h : x ^ 2 * y = 1
h_1 : x * y ^ 2 = y
h_2 : ¬y * x = 1
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] False propositions
  [eqc] Equivalence classes
  [linarith] Linarith assignment for `α`
```
```lean
example (x y : Nat) :
    x ^ 2 * y = 1 →
    x * y ^ 2 = y →
    y * x = 1 := by
  grind
```
```lean +error (name := ring100)
example [CommRing α] [IsCharP α 0] (d t c : α) (d_inv PSO3_inv : α) :
    d ^ 2 * (d + t - d * t - 2) * (d + t + d * t) = 0 →
    -d ^ 4 * (d + t - d * t - 2) *
      (2 * d + 2 * d * t - 4 * d * t ^ 2 + 2 * d * t^4 +
      2 * d^2 * t^4 - c * (d + t + d * t)) = 0 →
    d * d_inv = 1 →
    (d + t - d * t - 2) * PSO3_inv = 1 →
    t^2 = t + 1 := by
  grind (ringSteps := 100)
```
```leanOutput ring100
`grind` failed
case grind
α : Type u_1
inst : CommRing α
inst_1 : IsCharP α 0
d t c d_inv PSO3_inv : α
h : d ^ 2 * (d + t - d * t - 2) * (d + t + d * t) = 0
h_1 : -d ^ 4 * (d + t - d * t - 2) *
    (2 * d + 2 * d * t - 4 * d * t ^ 2 + 2 * d * t ^ 4 + 2 * d ^ 2 * t ^ 4 - c * (d + t + d * t)) =
  0
h_2 : d * d_inv = 1
h_3 : (d + t - d * t - 2) * PSO3_inv = 1
h_4 : ¬t ^ 2 = t + 1
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] True propositions
  [eqc] False propositions
  [eqc] Equivalence classes
  [ring] Ring `α`
  [limits] Thresholds reached
```
```leanOutput ring100
`grind` failed
case grind
α : Type u_1
inst : CommRing α
inst_1 : IsCharP α 0
d t c d_inv PSO3_inv : α
h : d ^ 2 * (d + t - d * t - 2) * (d + t + d * t) = 0
h_1 : -d ^ 4 * (d + t - d * t - 2) *
    (2 * d + 2 * d * t - 4 * d * t ^ 2 + 2 * d * t ^ 4 + 2 * d ^ 2 * t ^ 4 - c * (d + t + d * t)) =
  0
h_2 : d * d_inv = 1
h_3 : (d + t - d * t - 2) * PSO3_inv = 1
h_4 : ¬t ^ 2 = t + 1
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] True propositions
  [eqc] False propositions
  [eqc] Equivalence classes
  [ring] Ring `α`
  [limits] Thresholds reached
```
```lean
example (x y : Int) :
    x ^ 2 * y = 1 →
    x * y ^ 2 = y →
    some (y * x) = some 1 := by
  grind
``````lean -show
    variable {A : Prop} {B : Sort u}
    ```
```lean
example (c : Bool) (x y : Nat)
    (h : (if c then x else y) = 0) :
    x = 0 ∨ y = 0 := by
  grind
```
```lean +error (name := noSplitIte)
example (c : Bool) (x y : Nat)
    (h : (if c then x else y) = 0) :
    x = 0 ∨ y = 0 := by
  grind -splitIte
```
```leanOutput noSplitIte (expandTrace := eqc)
`grind` failed
case grind
c : Bool
x y : Nat
h : (if c = true then x else y) = 0
left : ¬x = 0
right : ¬y = 0
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] False propositions
    [prop] x = 0
    [prop] y = 0
  [eqc] Equivalence classes
    [eqc] {0, if c = true then x else y}
  [cutsat] Assignment satisfying linear constraints
```
```leanOutput noSplitIte (expandTrace := eqc)
`grind` failed
case grind
c : Bool
x y : Nat
h : (if c = true then x else y) = 0
left : ¬x = 0
right : ¬y = 0
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] False propositions
    [prop] x = 0
    [prop] y = 0
  [eqc] Equivalence classes
    [eqc] {0, if c = true then x else y}
  [cutsat] Assignment satisfying linear constraints
```
```lean +error (name := noSplitsAtAll)
example (c : Bool) (x y : Nat)
    (h : (if c then x else y) = 0) :
    x = 0 ∨ y = 0 := by
  grind (splits := 0)
```
```leanOutput noSplitsAtAll (expandTrace := eqc)
`grind` failed
case grind
c : Bool
x y : Nat
h : (if c = true then x else y) = 0
left : ¬x = 0
right : ¬y = 0
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] False propositions
    [prop] x = 0
    [prop] y = 0
  [eqc] Equivalence classes
    [eqc] {0, if c = true then x else y}
  [cutsat] Assignment satisfying linear constraints
  [limits] Thresholds reached
```
```leanOutput noSplitsAtAll (expandTrace := eqc)
`grind` failed
case grind
c : Bool
x y : Nat
h : (if c = true then x else y) = 0
left : ¬x = 0
right : ¬y = 0
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] False propositions
    [prop] x = 0
    [prop] y = 0
  [eqc] Equivalence classes
    [eqc] {0, if c = true then x else y}
  [cutsat] Assignment satisfying linear constraints
  [limits] Thresholds reached
```
```lean
example (c : Bool) (x y : Nat)
    (h : (if c then x else y) = 0) :
    x = 0 ∨ y = 0 := by
  grind (splits := 1)
```
```lean +error (name := noSplitMatch)
example (h : y = match x with | 0 => 1 | _ => 2) :
    y > 0 := by
  grind -splitMatch
```
```leanOutput noSplitMatch (expandTrace := eqc)
`grind` failed
case grind
y x : Nat
h : y =
  match x with
  | 0 => 1
  | x => 2
h_1 : y = 0
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] True propositions
    [prop] (x = 0 → False) →
          (match x with
            | 0 => 1
            | x => 2) =
            2
  [eqc] Equivalence classes
    [eqc] {y,
        0,
        match x with
        | 0 => 1
        | x => 2}
    [eqc] {x = 0 → False, (fun x_0 => x_0 = 0 → False) x, x = 0 → False}
  [ematch] E-matching patterns
  [cutsat] Assignment satisfying linear constraints

[grind] Diagnostics
```
```leanOutput noSplitMatch (expandTrace := eqc)
`grind` failed
case grind
y x : Nat
h : y =
  match x with
  | 0 => 1
  | x => 2
h_1 : y = 0
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] True propositions
    [prop] (x = 0 → False) →
          (match x with
            | 0 => 1
            | x => 2) =
            2
  [eqc] Equivalence classes
    [eqc] {y,
        0,
        match x with
        | 0 => 1
        | x => 2}
    [eqc] {x = 0 → False, (fun x_0 => x_0 = 0 → False) x, x = 0 → False}
  [ematch] E-matching patterns
  [cutsat] Assignment satisfying linear constraints

[grind] Diagnostics
```
```lean
example (h : y = match x with | 0 => 1 | _ => 2) :
    y > 0 := by
  grind
```
```lean
inductive Not30 : Nat → Prop where
  | gt : x > 30 → Not30 x
  | lt : x < 30 → Not30 x
```
```lean +error (name := not30fail)
example : Not30 n → n ≠ 30 := by grind
```
```leanOutput not30fail (expandTrace := eqc)
`grind` failed
case grind
n : Nat
h : Not30 n
h_1 : n = 30
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] True propositions
    [prop] Not30 n
  [eqc] Equivalence classes
    [eqc] {n, 30}
  [cutsat] Assignment satisfying linear constraints
```
```leanOutput not30fail (expandTrace := eqc)
`grind` failed
case grind
n : Nat
h : Not30 n
h_1 : n = 30
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] True propositions
    [prop] Not30 n
  [eqc] Equivalence classes
    [eqc] {n, 30}
  [cutsat] Assignment satisfying linear constraints
```
```lean
attribute [grind cases] Not30

example : Not30 n → n ≠ 30 := by grind
```
```lean (name := blah)
@[grind cases]
inductive Even : Nat → Prop
  | zero : Even 0
  | step : Even n → Even (n + 2)

attribute [grind cases] Even

example (h : Even 5) : False := by
  grind

set_option trace.grind.split true in
example (h : Even (n + 2)) : Even n := by
  grind
``````lean -show
variable {a a' : α} {b b' : β} {f : α → β → γ}
```
```lean -show
variable {t₁ t₂ : α} {h : t₁ = t₂} {a : α} {f : α → β} {g : β → β}
```
```lean
example {α} (f g : α → α) (x y : α)
    (h₁ : x = y) (h₂ : f y = g y) :
    f x = g x := by
  grind
```
```lean
example (a b c : Nat) (h : a = b) : (a, c) = (b, c) := by
  grind
```
```lean -show
variable {t₁ t₂ : α} {h : t₁ = t₂} {a : α} {f : α → β} {g : β → β}
``````lean -show
  variable {A B : Prop}
  ```
```lean -show
  variable {x x' : α} {y y' : β} {h : (x, y) = (x', y')} {a : α}
  ```
```lean -show
  variable {h : α = β} {a : α}
  ```
```lean -show
  variable {α : Type u} {β : Type v} {a : α} {b : β}
  structure S α β where
    x : α
    y : β
  variable {p : S α β}

  -- Check that struct eta fails
  /--
  error: `grind` failed
  case grind
  α : Type u
  β : Type v
  a : α
  b : β
  p : S α β
  h : ¬p = { x := p.x, y := p.y }
  ⊢ False
  [grind] Goal diagnostics
    [facts] Asserted facts
      [prop] ¬p = { x := p.x, y := p.y }
    [eqc] False propositions
      [prop] p = { x := p.x, y := p.y }
  -/
  #guard_msgs (whitespace := lax) in
  example : p = ⟨p.1, p.2⟩ := by grind

  -- They are defeq
  example : p = ⟨p.1, p.2⟩ := by rfl

  attribute [grind ext] S

  example : p = ⟨p.1, p.2⟩ := by grind
  ```
```lean -show
namespace ExamplePropagators
```
```lean -keep

/-- Propagate equalities *upwards* for conjunctions. -/
builtin_grind_propagator propagateAndUp ↑And := fun e => do
  let_expr And a b := e | return ()
  if (← isEqTrue a) then
    -- a = True  ⇒  (a ∧ b) = b
    pushEq e b <|
      mkApp3 (mkConst ``Grind.and_eq_of_eq_true_left)
        a b (← mkEqTrueProof a)
  else if (← isEqTrue b) then
    -- b = True  ⇒  (a ∧ b) = a
    pushEq e a <|
      mkApp3 (mkConst ``Grind.and_eq_of_eq_true_right)
        a b (← mkEqTrueProof b)
  else if (← isEqFalse a) then
    -- a = False  ⇒  (a ∧ b) = False
    pushEqFalse e <|
      mkApp3 (mkConst ``Grind.and_eq_of_eq_false_left)
        a b (← mkEqFalseProof a)
  else if (← isEqFalse b) then
    -- b = False  ⇒  (a ∧ b) = False
    pushEqFalse e <|
      mkApp3 (mkConst ``Grind.and_eq_of_eq_false_right)
        a b (← mkEqFalseProof b)

/--
Truth flows *down* when the whole `And` is proven `True`.
-/
builtin_grind_propagator propagateAndDown ↓And :=
  fun e => do
  if (← isEqTrue e) then
    let_expr And a b := e | return ()
    let h ← mkEqTrueProof e
    -- (a ∧ b) = True  ⇒  a = True
    pushEqTrue a <| mkApp3
      (mkConst ``Grind.eq_true_of_and_eq_true_left) a b h
    -- (a ∧ b) = True  ⇒  B = True
    pushEqTrue b <| mkApp3
      (mkConst ``Grind.eq_true_of_and_eq_true_right) a b h
```
```lean -show
end ExamplePropagators
```
```lean -show
variable {A B : Prop} {a b : α}
```
```lean
-- Boolean connective: a && !a is always false.
example (a : Bool) : (a && !a) = false := by
  grind

-- Conditional (ite):
-- once the condition is true, ite picks the 'then' branch.
example (c : Bool) (t e : Nat) (h : c = true) :
    (if c then t else e) = t := by
  grind

-- Negation propagates truth downwards.
example (a : Bool) (h : (!a) = true) : a = false := by
  grind
```
```lean -show
-- Test to ensure that this section is uncommented when the command is implemented
/--
error: elaboration function for `Lean.Parser.«command_Grind_propagator___(_):=_»` has not been implemented
-/
#guard_msgs in
grind_propagator ↑x(y) := _
```
```lean +error (name := missing)
example :
    x = y ∧ y = z →
    w = x ∨ w = v →
    w = z := by
  grind
```
```leanOutput missing (expandTrace := eqc)
`grind` failed
case grind
α : Sort u_1
x y z w v : α
left : x = y
right : y = z
h_1 : w = x ∨ w = v
h_2 : ¬w = z
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] True propositions
    [prop] w = x ∨ w = v
    [prop] w = v
  [eqc] False propositions
    [prop] w = x
    [prop] w = z
  [eqc] Equivalence classes
    [eqc] {x, y, z}
    [eqc] {w, v}
```
```leanOutput missing (expandTrace := eqc)
`grind` failed
case grind
α : Sort u_1
x y z w v : α
left : x = y
right : y = z
h_1 : w = x ∨ w = v
h_2 : ¬w = z
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] True propositions
    [prop] w = x ∨ w = v
    [prop] w = v
  [eqc] False propositions
    [prop] w = x
    [prop] w = z
  [eqc] Equivalence classes
    [eqc] {x, y, z}
    [eqc] {w, v}
``````lean
example {x y : Int} : 2 * x + 4 * y ≠ 5 := by
  grind
```
```lean
example {x y : Int} :
    2 * x + 3 * y = 0 →
    1 ≤ x →
    y < 1 := by
  grind
```
```lean
example (a b : Int) :
    2 ∣ a + 1 →
    2 ∣ b + a →
    ¬ 2 ∣ b + 2 * a := by
  grind
```
```lean +error (name := noCutsat)
example (a b : Int) :
    2 ∣ a + 1 →
    2 ∣ b + a →
    ¬ 2 ∣ b + 2 * a := by
  grind -cutsat
```
```leanOutput noCutsat
`grind` failed
case grind
a b : Int
h : 2 ∣ a + 1
h_1 : 2 ∣ a + b
h_2 : 2 ∣ 2 * a + b
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] True propositions
  [linarith] Linarith assignment for `Int`
```
```leanOutput noCutsat
`grind` failed
case grind
a b : Int
h : 2 ∣ a + 1
h_1 : 2 ∣ a + b
h_2 : 2 ∣ 2 * a + b
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] True propositions
  [linarith] Linarith assignment for `Int`
```
```lean
example {x y : Int} :
    27 ≤ 13 * x + 11 * y →
    13 * x + 11 * y ≤ 30 →
    -10 ≤ 9 * x - 7 * y →
    9 * x - 7 * y > 4 := by
  grind
```
```lean +error (name := withqlia)
example {x y : Int} :
    27 ≤ 13 * x + 11 * y →
    13 * x + 11 * y ≤ 30 →
    -10 ≤ 9 * x - 7 * y →
    9 * x - 7 * y > 4 := by
  grind +qlia
```
```leanOutput withqlia (expandTrace := cutsat)
`grind` failed
case grind
x y : Int
h : -13 * x + -11 * y + 27 ≤ 0
h_1 : 13 * x + 11 * y + -30 ≤ 0
h_2 : -9 * x + 7 * y + -10 ≤ 0
h_3 : 9 * x + -7 * y + -4 ≤ 0
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] True propositions
  [cutsat] Assignment satisfying linear constraints
    [assign] x := 62/117
    [assign] y := 2
```
```leanOutput withqlia (expandTrace := cutsat)
`grind` failed
case grind
x y : Int
h : -13 * x + -11 * y + 27 ≤ 0
h_1 : 13 * x + 11 * y + -30 ≤ 0
h_2 : -9 * x + 7 * y + -10 ≤ 0
h_3 : 9 * x + -7 * y + -4 ≤ 0
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] True propositions
  [cutsat] Assignment satisfying linear constraints
    [assign] x := 62/117
    [assign] y := 2
```
```lean +error (name := nonlinear)
example (x : Int) : x * x ≥ 0 := by
  grind
```
```leanOutput nonlinear
`grind` failed
case grind
x : Int
h : x * x + 1 ≤ 0
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] True propositions
  [cutsat] Assignment satisfying linear constraints
```
```leanOutput nonlinear
`grind` failed
case grind
x : Int
h : x * x + 1 ≤ 0
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] True propositions
  [cutsat] Assignment satisfying linear constraints
```
```lean +error (name := nonlinear2)
example {y : Int} (x : Int) : y ≥ 0 := by
  grind
```
```leanOutput nonlinear
`grind` failed
case grind
x : Int
h : x * x + 1 ≤ 0
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] True propositions
  [cutsat] Assignment satisfying linear constraints
```
```leanOutput nonlinear
`grind` failed
case grind
x : Int
h : x * x + 1 ≤ 0
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] True propositions
  [cutsat] Assignment satisfying linear constraints
```
```lean +error (name := cutsatDiag)
example (x : Int) : x*x ≥ 0 := by
  set_option trace.grind.cutsat.assert true in
  grind
```
```leanOutput cutsatDiag
[grind.cutsat.assert] -1*「x ^ 2 + 1」 + 「x ^ 2」 + 1 = 0
[grind.cutsat.assert] 「x ^ 2」 + 1 ≤ 0
```
```leanOutput cutsatDiag
[grind.cutsat.assert] -1*「x ^ 2 + 1」 + 「x ^ 2」 + 1 = 0
[grind.cutsat.assert] 「x ^ 2」 + 1 ≤ 0
```
```lean
example (x y : Int) :
    x = y / 2 →
    y % 2 = 0 →
    y - 2 * x = 0 := by
  grind
```
```lean
example (a b : Nat)
    (h₁ : a + 1 ≠ a * b * a)
    (h₂ : a * a * b ≤ a + 1) :
    b * a ^ 2 < a + 1 := by
  grind
```
```lean
example (f : Int → Int) (x y : Int) :
    f x = 0 →
    0 ≤ y → y ≤ 1 → y ≠ 1 →
    f (x + y) = 0 := by
  grind
```
```lean +error (name := noMbtc)
example (f : Int → Int) (x y : Int) :
    f x = 0 →
    0 ≤ y → y ≤ 1 → y ≠ 1 →
    f (x + y) = 0 := by
  grind -mbtc
```
```leanOutput noMbtc
`grind` failed
case grind
f : Int → Int
x y : Int
h : f x = 0
h_1 : -1 * y ≤ 0
h_2 : y + -1 ≤ 0
h_3 : ¬y = 1
h_4 : ¬f (x + y) = 0
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] True propositions
  [eqc] False propositions
  [eqc] Equivalence classes
  [cutsat] Assignment satisfying linear constraints
  [ring] Ring `Int`
```
```leanOutput noMbtc
`grind` failed
case grind
f : Int → Int
x y : Int
h : f x = 0
h_1 : -1 * y ≤ 0
h_2 : y + -1 ≤ 0
h_3 : ¬y = 1
h_4 : ¬f (x + y) = 0
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] True propositions
  [eqc] False propositions
  [eqc] Equivalence classes
  [cutsat] Assignment satisfying linear constraints
  [ring] Ring `Int`
```
```lean
example (x y z : Nat) :
    x < y + z →
    y + 1 < z →
    z + x < 3 * z := by
  grind
```
```lean
example (a b c : Fin 11) : a ≤ 2 → b ≤ 3 → c = a + b → c ≤ 5 := by
  grind

example (a : Fin 2) : a ≠ 0 → a ≠ 1 → False := by
  grind

example (a b c : UInt64) : a ≤ 2 → b ≤ 3 → c - a - b = 0 → c ≤ 5 := by
  grind
```
```lean -show
variable {x y : Int}
``````lean
variable [LE α] [LT α] [Std.LawfulOrderLT α]  [Std.IsLinearOrder α]
variable [IntModule α] [OrderedAdd α]
```
```lean
example {a b : α} : 2 • a + b ≥ b + a + a := by grind

example {a b : α} (h : a ≤ b) : 3 • a + b ≤ 4 • b := by grind

example {a b c : α} :
    a = b + c →
    2 • b ≤ c →
    2 • a ≤ 3 • c := by
  grind

example {a b c d e : α} :
    2 • a + b ≥ 0 →
    b ≥ 0 → c ≥ 0 → d ≥ 0 → e ≥ 0 →
    a ≥ 3 • c → c ≥ 6 • e → d - 5 • e ≥ 0 →
    a + b + 3 • c + d + 2 • e < 0 →
    False := by
  grind
```
```lean
variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R]
variable [CommRing R] [OrderedRing R]
```
```lean
example (a b : R) (h : a * b ≤ 1) : b * 3 • a + 1 ≤ 4 := by grind

example (a b c d e f : R) :
    2 • a + b ≥ 1 →
    b ≥ 0 → c ≥ 0 → d ≥ 0 → e • f ≥ 0 →
    a ≥ 3 • c →
    c ≥ 6 • e • f → d - f * e * 5 ≥ 0 →
    a + b + 3 • c + d + 2 • e • f < 0 →
    False := by
  grind
``````lean -show
open Std
```
```lean
/--
An if-expression is either boolean literal, a
numbered variable, or an if-then-else expression
where each subexpression is an if-expression.
-/
inductive IfExpr
  | lit : Bool → IfExpr
  | var : Nat → IfExpr
  | ite : IfExpr → IfExpr → IfExpr → IfExpr
deriving DecidableEq
```
```lean
namespace IfExpr

/--
An if-expression has a "nested if" if it contains
an if-then-else where the "if" is itself an if-then-else.
-/
def hasNestedIf : IfExpr → Bool
  | lit _ => false
  | var _ => false
  | ite (ite _ _ _) _ _ => true
  | ite _ t e => t.hasNestedIf || e.hasNestedIf

/--
An if-expression has a "constant if" if it contains
an if-then-else where the "if" is itself a literal.
-/
def hasConstantIf : IfExpr → Bool
  | lit _ => false
  | var _ => false
  | ite (lit _) _ _ => true
  | ite i t e =>
    i.hasConstantIf || t.hasConstantIf || e.hasConstantIf

/--
An if-expression has a "redundant if" if
it contains an if-then-else where
the "then" and "else" clauses are identical.
-/
def hasRedundantIf : IfExpr → Bool
  | lit _ => false
  | var _ => false
  | ite i t e => t == e || i.hasRedundantIf ||
      t.hasRedundantIf || e.hasRedundantIf

/--
All the variables appearing in an if-expressions,
read left to right, without removing duplicates.
-/
def vars : IfExpr → List Nat
  | lit _ => []
  | var i => [i]
  | ite i t e => i.vars ++ t.vars ++ e.vars

/--
A helper function to specify that two lists are disjoint.
-/
def _root_.List.disjoint {α} [DecidableEq α] :
    List α → List α → Bool
  | [], _ => true
  | x::xs, ys => x ∉ ys && xs.disjoint ys

/--
An if expression evaluates each variable at most once if
for each if-then-else the variables in the "if" clause
are disjoint from the variables in the "then" clause
and the variables in the "if" clause
are disjoint from the variables in the "else" clause.
-/
def disjoint : IfExpr → Bool
  | lit _ => true
  | var _ => true
  | ite i t e =>
      i.vars.disjoint t.vars && i.vars.disjoint e.vars &&
        i.disjoint && t.disjoint && e.disjoint

/--
An if expression is "normalized" if it has
no nested, constant, or redundant ifs,
and it evaluates each variable at most once.
-/
def normalized (e : IfExpr) : Bool :=
  !e.hasNestedIf && !e.hasConstantIf &&
    !e.hasRedundantIf && e.disjoint

/--
The evaluation of an if expression
at some assignment of variables.
-/
def eval (f : Nat → Bool) : IfExpr → Bool
  | lit b => b
  | var i => f i
  | ite i t e => bif i.eval f then t.eval f else e.eval f

end IfExpr
```
```lean
def IfNormalization : Type :=
  { Z : IfExpr → IfExpr // ∀ e, (Z e).normalized ∧ (Z e).eval = e.eval }
```
```lean
namespace IfExpr
```
```lean +error (name := failed_to_show_termination)
def normalize (assign : Std.HashMap Nat Bool) :
    IfExpr → IfExpr
  | lit b => lit b
  | var v =>
    match assign[v]? with
    | none => var v
    | some b => lit b
  | ite (lit true)  t _ => normalize assign t
  | ite (lit false) _ e => normalize assign e
  | ite (ite a b c) t e =>
    normalize assign (ite a (ite b t e) (ite c t e))
  | ite (var v)     t e =>
    match assign[v]? with
    | none =>
      let t' := normalize (assign.insert v true) t
      let e' := normalize (assign.insert v false) e
      if t' = e' then t' else ite (var v) t' e'
    | some b => normalize assign (ite (lit b) t e)

```
```leanOutput failed_to_show_termination (stopAt := "Could not find a decreasing measure.")
fail to show termination for
  IfExpr.normalize
with errors
failed to infer structural recursion:
Cannot use parameter assign:
  the type HashMap Nat Bool does not have a `.brecOn` recursor
Cannot use parameter #2:
  failed to eliminate recursive application
    normalize assign (a.ite (b.ite t e) (c.ite t e))


Could not find a decreasing measure.
```
```leanOutput failed_to_show_termination (stopAt := "Could not find a decreasing measure.")
fail to show termination for
  IfExpr.normalize
with errors
failed to infer structural recursion:
Cannot use parameter assign:
  the type HashMap Nat Bool does not have a `.brecOn` recursor
Cannot use parameter #2:
  failed to eliminate recursive application
    normalize assign (a.ite (b.ite t e) (c.ite t e))


Could not find a decreasing measure.
```
```lean
@[simp] def normSize : IfExpr → Nat
  | lit _ => 0
  | var _ => 1
  | .ite i t e => 2 * normSize i + max (normSize t) (normSize e) + 1
```
```lean
def normalize (assign : Std.HashMap Nat Bool) :
    IfExpr → IfExpr
  | lit b => lit b
  | var v =>
    match assign[v]? with
    | none => var v
    | some b => lit b
  | ite (lit true)  t _ => normalize assign t
  | ite (lit false) _ e => normalize assign e
  | ite (ite a b c) t e =>
    normalize assign (ite a (ite b t e) (ite c t e))
  | ite (var v)     t e =>
    match assign[v]? with
    | none =>
      let t' := normalize (assign.insert v true) t
      let e' := normalize (assign.insert v false) e
      if t' = e' then t' else ite (var v) t' e'
    | some b => normalize assign (ite (lit b) t e)
termination_by e => e.normSize
```
```lean -keep
theorem normalize_spec
    (assign : Std.HashMap Nat Bool) (e : IfExpr) :
    (normalize assign e).normalized
      ∧ (∀ f, (normalize assign e).eval f =
          e.eval fun w => assign[w]?.getD (f w))
      ∧ ∀ (v : Nat),
          v ∈ vars (normalize assign e) → ¬ v ∈ assign :=
  sorry
```
```lean
-- We tell `grind` to unfold our definitions above.
attribute [local grind]
  normalized hasNestedIf hasConstantIf hasRedundantIf
  disjoint vars eval List.disjoint

theorem normalize_spec
    (assign : Std.HashMap Nat Bool) (e : IfExpr) :
    (normalize assign e).normalized
      ∧ (∀ f, (normalize assign e).eval f =
          e.eval fun w => assign[w]?.getD (f w))
      ∧ ∀ (v : Nat),
          v ∈ vars (normalize assign e) → ¬ v ∈ assign := by
  fun_induction normalize with grind
```
```lean
example (assign : Std.HashMap Nat Bool) (e : IfExpr) :
    (normalize assign e).normalized
      ∧ (∀ f, (normalize assign e).eval f =
          e.eval fun w => assign[w]?.getD (f w))
      ∧ ∀ (v : Nat), v ∈ vars (normalize assign e) →
          assign.contains v = false := by
  fun_induction normalize with grind
```
```lean
example (assign : Std.HashMap Nat Bool) (e : IfExpr) :
    (normalize assign e).normalized
      ∧ (∀ f, (normalize assign e).eval f =
          e.eval fun w => assign[w]?.getD (f w))
      ∧ ∀ (v : Nat),
          v ∈ vars (normalize assign e) → assign[v]? = none := by
  fun_induction normalize with grind
```
```lean -show
-- We have to repeat these annotations because we've rolled back the environment to before we defined `normalize`.
attribute [local grind]
  normalized hasNestedIf hasConstantIf hasRedundantIf
  disjoint vars eval List.disjoint
```
```lean
def normalize (assign : Std.TreeMap Nat Bool) :
    IfExpr → IfExpr
  | lit b => lit b
  | var v =>
    match assign[v]? with
    | none => var v
    | some b => lit b
  | ite (lit true)  t _ => normalize assign t
  | ite (lit false) _ e => normalize assign e
  | ite (ite a b c) t e =>
    normalize assign (ite a (ite b t e) (ite c t e))
  | ite (var v)     t e =>
    match assign[v]? with
    | none =>
      let t' := normalize (assign.insert v true) t
      let e' := normalize (assign.insert v false) e
      if t' = e' then t' else ite (var v) t' e'
    | some b => normalize assign (ite (lit b) t e)
termination_by e => e.normSize

theorem normalize_spec
    (assign : Std.TreeMap Nat Bool) (e : IfExpr) :
    (normalize assign e).normalized
      ∧ (∀ f, (normalize assign e).eval f =
          e.eval fun w => assign[w]?.getD (f w))
      ∧ ∀ (v : Nat),
          v ∈ vars (normalize assign e) → ¬ v ∈ assign := by
  fun_induction normalize with grind
```
```lean -show
end IfExpr
``````lean -show
variable {α : Type u} [BEq α] [Hashable α]
```
```lean
macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| grind)

open Std

structure IndexMap
    (α : Type u) (β : Type v) [BEq α] [Hashable α] where
  private indices : HashMap α Nat
  private keys : Array α
  private values : Array β
  private size_keys' : keys.size = values.size := by grind
  private WF : ∀ (i : Nat) (a : α),
    keys[i]? = some a ↔ indices[a]? = some i := by grind

namespace IndexMap

variable {α : Type u} {β : Type v} [BEq α] [Hashable α]
variable {m : IndexMap α β} {a : α} {b : β} {i : Nat}

@[inline] def size (m : IndexMap α β) : Nat :=
  m.values.size

@[local grind =] private theorem size_keys : m.keys.size = m.size :=
  m.size_keys'

def emptyWithCapacity (capacity := 8) : IndexMap α β where
  indices := HashMap.emptyWithCapacity capacity
  keys := Array.emptyWithCapacity capacity
  values := Array.emptyWithCapacity capacity

instance : EmptyCollection (IndexMap α β) where
  emptyCollection := emptyWithCapacity

instance : Inhabited (IndexMap α β) where
  default := ∅

@[inline] def contains (m : IndexMap α β)
    (a : α) : Bool :=
  m.indices.contains a

instance : Membership α (IndexMap α β) where
  mem m a := a ∈ m.indices

instance {m : IndexMap α β} {a : α} : Decidable (a ∈ m) :=
  inferInstanceAs (Decidable (a ∈ m.indices))

@[local grind] private theorem mem_indices_of_mem
    {m : IndexMap α β} {a : α} :
    a ∈ m ↔ a ∈ m.indices := Iff.rfl

@[inline] def findIdx? (m : IndexMap α β) (a : α) : Option Nat :=
  m.indices[a]?

@[inline] def findIdx (m : IndexMap α β) (a : α)
    (h : a ∈ m := by get_elem_tactic) : Nat :=
  m.indices[a]

@[inline] def getIdx? (m : IndexMap α β) (i : Nat) : Option β :=
  m.values[i]?

@[inline] def getIdx (m : IndexMap α β) (i : Nat)
    (h : i < m.size := by get_elem_tactic) : β :=
  m.values[i]

variable [LawfulBEq α] [LawfulHashable α]

attribute [local grind _=_] IndexMap.WF

private theorem getElem_indices_lt {h : a ∈ m} : m.indices[a] < m.size := by
  have : m.indices[a]? = some m.indices[a] := by grind
  grind

grind_pattern getElem_indices_lt => m.indices[a]

attribute [local grind] size

instance : GetElem? (IndexMap α β) α β (fun m a => a ∈ m) where
  getElem m a h :=
    m.values[m.indices[a]]
  getElem? m a :=
    m.indices[a]?.bind (fun i => (m.values[i]?))
  getElem! m a :=
    m.indices[a]?.bind (fun i => (m.values[i]?)) |>.getD default

@[local grind] private theorem getElem_def
    (m : IndexMap α β) (a : α) (h : a ∈ m) :
    m[a] = m.values[m.indices[a]'h] :=
  rfl
@[local grind] private theorem getElem?_def
    (m : IndexMap α β) (a : α) :
    m[a]? = m.indices[a]?.bind (fun i => (m.values[i]?)) :=
  rfl
@[local grind] private theorem getElem!_def
    [Inhabited β] (m : IndexMap α β) (a : α) :
    m[a]! = (m.indices[a]?.bind (m.values[·]?)).getD default :=
  rfl

instance : LawfulGetElem (IndexMap α β) α β (fun m a => a ∈ m) where
  getElem?_def := by grind
  getElem!_def := by grind

@[inline] def insert [LawfulBEq α] (m : IndexMap α β) (a : α) (b : β) :
    IndexMap α β :=
  match h : m.indices[a]? with
  | some i =>
    { indices := m.indices
      keys := m.keys.set i a
      values := m.values.set i b }
  | none =>
    { indices := m.indices.insert a m.size
      keys := m.keys.push a
      values := m.values.push b }

instance [LawfulBEq α] : Singleton (α × β) (IndexMap α β) :=
    ⟨fun ⟨a, b⟩ => (∅ : IndexMap α β).insert a b⟩

instance [LawfulBEq α] : Insert (α × β) (IndexMap α β) :=
    ⟨fun ⟨a, b⟩ s => s.insert a b⟩

instance [LawfulBEq α] : LawfulSingleton (α × β) (IndexMap α β) :=
    ⟨fun _ => rfl⟩

@[local grind] private theorem WF'
    (i : Nat) (a : α) (h₁ : i < m.keys.size) (h₂ : a ∈ m) :
    m.keys[i] = a ↔ m.indices[a] = i := by
  have := m.WF i a
  grind

/--
Erase the key-value pair with the given key,
moving the last pair into its place in the order.
If the key is not present, the map is unchanged.
-/
@[inline] def eraseSwap (m : IndexMap α β) (a : α) : IndexMap α β :=
  match h : m.indices[a]? with
  | some i =>
    if w : i = m.size - 1 then
      { indices := m.indices.erase a
        keys := m.keys.pop
        values := m.values.pop }
    else
      let lastKey := m.keys.back
      let lastValue := m.values.back
      { indices := (m.indices.erase a).insert lastKey i
        keys := m.keys.pop.set i lastKey
        values := m.values.pop.set i lastValue }
  | none => m

/-! ### Verification theorems -/

attribute [local grind] getIdx findIdx insert

@[grind] theorem getIdx_findIdx (m : IndexMap α β) (a : α) (h : a ∈ m) :
    m.getIdx (m.findIdx a) = m[a] := by grind

@[grind] theorem mem_insert (m : IndexMap α β) (a a' : α) (b : β) :
    a' ∈ m.insert a b ↔ a' = a ∨ a' ∈ m := by
  grind

@[grind] theorem getElem_insert
    (m : IndexMap α β) (a a' : α) (b : β) (h : a' ∈ m.insert a b) :
    (m.insert a b)[a'] = if h' : a' == a then b else m[a'] := by
  grind

@[grind] theorem findIdx_insert_self
    (m : IndexMap α β) (a : α) (b : β) :
    (m.insert a b).findIdx a =
      if h : a ∈ m then m.findIdx a else m.size := by
  grind

end IndexMap
``````lean
axiom R : Type


@[instance] axiom instCommRingR : Lean.Grind.CommRing R


axiom sin : R → R
axiom cos : R → R
axiom trig_identity : ∀ x, (cos x)^2 + (sin x)^2 = 1
```
```lean
grind_pattern trig_identity => cos x
grind_pattern trig_identity => sin x
```
```lean -keep
grind_pattern trig_identity => cos x, sin x
```
```lean -show
variable {x : R}
```
```lean
example : (cos x + sin x)^2 = 2 * cos x * sin x + 1 := by
  grind
```
```lean
example (f : R → Nat) :
    f ((cos x + sin x)^2) = f (2 * cos x * sin x + 1) := by
  grind
```
```lean -show
variable (f : R → Nat) (n : Nat)
```
```lean
example (f : R → Nat) :
    4 * f ((cos x + sin x)^2) ≠ 2 + f (2 * cos x * sin x + 1) := by
  grind
```
```lean
example (f : R → Nat) :
    max 3 (4 * f ((cos x + sin x)^2)) ≠
      2 + f (2 * cos x * sin x + 1) := by
  grind
```