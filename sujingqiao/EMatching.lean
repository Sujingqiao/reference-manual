```lean
def f (a : Nat) : Nat :=
  a + 1

def g (a : Nat) : Nat :=
  a - 1

@[grind =]
theorem gf (x : Nat) : g (f x) = x := by
  simp [f, g]
```
```lean -show
variable {x a b : Nat}
```
```lean
example {a b} (h : f b = a) : g a = b := by
  grind
```
```lean
def f (a : Nat) : Nat :=
  a + 1

def g (a : Nat) : Nat :=
  a - 1

@[grind =]
theorem gf (x : Nat) : g (f x) = x := by
  simp [f, g]
```
```lean +error (name := restrictivePattern)
example (h₁ : f b = a) (h₂ : f c = a) : b = c := by
  grind
```
```leanOutput restrictivePattern (expandTrace := eqc)
`grind` failed
case grind
b a c : Nat
h₁ : f b = a
h₂ : f c = a
h : ¬b = c
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] False propositions
    [prop] b = c
  [eqc] Equivalence classes
    [eqc] {a, f b, f c}
```
```leanOutput restrictivePattern (expandTrace := eqc)
`grind` failed
case grind
b a c : Nat
h₁ : f b = a
h₂ : f c = a
h : ¬b = c
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] False propositions
    [prop] b = c
  [eqc] Equivalence classes
    [eqc] {a, f b, f c}
```
```lean
grind_pattern gf => f x

example {a b c} (h₁ : f b = a) (h₂ : f c = a) : b = c := by
  grind
```
```lean (name := ematchInstanceTrace)
example (h₁ : f b = a) (h₂ : f c = a) : b = c := by
  set_option trace.grind.ematch.instance true in
  grind
```
```leanOutput ematchInstanceTrace
[grind.ematch.instance] gf: g (f c) = c
[grind.ematch.instance] gf: g (f b) = b
```
```leanOutput ematchInstanceTrace
[grind.ematch.instance] gf: g (f c) = c
[grind.ematch.instance] gf: g (f b) = b
```
```lean
opaque R : Int → Int → Prop
axiom Rtrans {x y z : Int} : R x y → R y z → R x z
```
```lean
grind_pattern Rtrans => R x y, R y z

example {a b c d} : R a b → R b c → R c d → R a d := by
  grind
```
```lean -show
variable {x y z a b c d : Int}
```
```lean -show
variable {α} {a b : α} [Inv α]
```
```lean
@[grind ←=]
theorem inv_eq [One α] [Mul α] [Inv α] {a b : α}
    (w : a * b = 1) : a⁻¹ = b :=
  sorry
```
```lean
structure Point where
  x : Int
  y : Int
```
```lean +error (name := noExt)
example (p : Point) : p = ⟨p.x, p.y⟩ := by grind
```
```leanOutput noExt
`grind` failed
case grind
p : Point
h : ¬p = { x := p.x, y := p.y }
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] False propositions
```
```leanOutput noExt
`grind` failed
case grind
p : Point
h : ¬p = { x := p.x, y := p.y }
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] False propositions
```
```lean
def Point.swap (p : Point) : Point := ⟨p.y, p.x⟩
```
```lean +error (name := noExt')
theorem swap_swap_eq_id : Point.swap ∘ Point.swap = id := by
  unfold Point.swap
  grind
```
```leanOutput noExt'
`grind` failed
case grind
h : ¬((fun p => { x := p.y, y := p.x }) ∘ fun p => { x := p.y, y := p.x }) = id
w : Point
h_1 : ¬{ x := w.x, y := w.y } = id w
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] True propositions
  [eqc] False propositions
  [eqc] Equivalence classes
  [cases] Case analyses
  [ematch] E-matching patterns

[grind] Diagnostics
```
```leanOutput noExt'
`grind` failed
case grind
h : ¬((fun p => { x := p.y, y := p.x }) ∘ fun p => { x := p.y, y := p.x }) = id
w : Point
h_1 : ¬{ x := w.x, y := w.y } = id w
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] True propositions
  [eqc] False propositions
  [eqc] Equivalence classes
  [cases] Case analyses
  [ematch] E-matching patterns

[grind] Diagnostics
```
```lean
attribute [grind ext] Point

example (p : Point) : p = ⟨p.x, p.y⟩ := by
  grind

theorem swap_swap_eq_id' : Point.swap ∘ Point.swap = id := by
  unfold Point.swap
  grind
```
```lean
theorem div_trans {n k j : Nat} : n ∣ k → k ∣ j → n ∣ j := by
  intro ⟨d₁, p₁⟩ ⟨d₂, p₂⟩
  exact ⟨d₁ * d₂, by rw [p₂, p₁, Nat.mul_assoc]⟩
```
```lean (name := grindHuh)
attribute [grind? →] div_trans
```
```leanOutput grindHuh
div_trans: [@Dvd.dvd `[Nat] `[Nat.instDvd] #4 #3, @Dvd.dvd `[Nat] `[Nat.instDvd] #3 #2]
```
```leanOutput grindHuh
div_trans: [@Dvd.dvd `[Nat] `[Nat.instDvd] #4 #3, @Dvd.dvd `[Nat] `[Nat.instDvd] #3 #2]
```
```lean
axiom p : Nat → Nat
axiom q : Nat → Nat
```
```lean (name := h1)
@[grind? →] theorem h₁ (w : 7 = p (q x)) : p (x + 1) = q x := sorry
```
```leanOutput h1
h₁: [q #1]
```
```leanOutput h1
h₁: [q #1]
```
```lean -show
axiom p : Nat → Nat
axiom q : Nat → Nat
```
```lean (name := h2)
set_option trace.grind.debug.ematch.pattern true in
@[grind? ←] theorem h₂ (w : 7 = p (q x)) : p (x + 1) = q x := sorry
```
```leanOutput h2
h₂: [p (#1 + 1)]
```
```leanOutput h2
h₂: [p (#1 + 1)]
```
```lean -show
axiom p : Nat → Nat
axiom q : Nat → Nat
```
```lean (name := h3)
@[grind? _=_] theorem h₃ (w : 7 = p (q x)) : p (x + 1) = q x := sorry
```
```leanOutput h3
h₃: [q #1]
```
```leanOutput h3
h₃: [q #1]
```
```leanOutput h3
h₃: [p (#1 + 1)]
```
```leanOutput h3
h₃: [p (#1 + 1)]
```
```lean -show
axiom p : Nat → Nat
axiom q : Nat → Nat
```
```lean (name := h4)
@[grind?] theorem h₄ (w : p x = q y) : p (x + 2) = 7 := sorry
```
```leanOutput h4
h₄: [p (#2 + 2), q #1]
```
```leanOutput h4
h₄: [p (#2 + 2), q #1]
```
```lean -show
axiom p : Nat → Nat
axiom q : Nat → Nat
```
```lean (name := h5) +error
@[grind? ←] theorem h₅ (w : p x = q y) : p (x + 2) = 7 := sorry
```
```leanOutput h5
`@[grind ←] theorem h₅` failed to find patterns in the theorem's conclusion, consider using different options or the `grind_pattern` command
```
```leanOutput h5
`@[grind ←] theorem h₅` failed to find patterns in the theorem's conclusion, consider using different options or the `grind_pattern` command
```
```lean -show
axiom p : Nat → Nat
axiom q : Nat → Nat
```
```lean (name := h6)
@[grind? =>] theorem h₆
    (_ : q (y + 2) = q y)
    (_ : q (y + 1) = q y) :
    p (x + 2) = 7 :=
  sorry
```
```leanOutput h6
h₆: [q (#3 + 2), p (#2 + 2)]
```
```leanOutput h6
h₆: [q (#3 + 2), p (#2 + 2)]
```
```lean (name := ematchUnboundedPat)
def s (x : Nat) := 0

@[grind? =] theorem s_eq (x : Nat) : s x = s (x + 1) :=
  rfl
```
```leanOutput ematchUnboundedPat
s_eq: [s #0]
```
```leanOutput ematchUnboundedPat
s_eq: [s #0]
```
```lean +error (name := ematchUnbounded)
example : s 0 > 0 := by
  grind
```
```leanOutput ematchUnbounded (expandTrace := limits) (expandTrace := ematch) (expandTrace := facts)
`grind` failed
case grind
h : s 0 = 0
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] s 0 = 0
    [prop] s 0 = s 1
    [prop] s 1 = s 2
    [prop] s 2 = s 3
    [prop] s 3 = s 4
    [prop] s 4 = s 5
  [eqc] Equivalence classes
  [ematch] E-matching patterns
    [thm] s_eq: [s #0]
  [cutsat] Assignment satisfying linear constraints
  [limits] Thresholds reached
    [limit] maximum number of E-matching rounds has been reached, threshold: `(ematch := 5)`

[grind] Diagnostics
```
```leanOutput ematchUnbounded (expandTrace := limits) (expandTrace := ematch) (expandTrace := facts)
`grind` failed
case grind
h : s 0 = 0
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] s 0 = 0
    [prop] s 0 = s 1
    [prop] s 1 = s 2
    [prop] s 2 = s 3
    [prop] s 3 = s 4
    [prop] s 4 = s 5
  [eqc] Equivalence classes
  [ematch] E-matching patterns
    [thm] s_eq: [s #0]
  [cutsat] Assignment satisfying linear constraints
  [limits] Thresholds reached
    [limit] maximum number of E-matching rounds has been reached, threshold: `(ematch := 5)`

[grind] Diagnostics
```
```lean +error (name := ematchUnbounded2)
example : s 0 > 0 := by
  grind (ematch := 20)
```
```leanOutput ematchUnbounded2 (expandTrace := limits) (expandTrace := ematch) (expandTrace := facts)
`grind` failed
case grind
h : s 0 = 0
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] s 0 = 0
    [prop] s 0 = s 1
    [prop] s 1 = s 2
    [prop] s 2 = s 3
    [prop] s 3 = s 4
    [prop] s 4 = s 5
    [prop] s 5 = s 6
    [prop] s 6 = s 7
    [prop] s 7 = s 8
  [eqc] Equivalence classes
  [ematch] E-matching patterns
    [thm] s_eq: [s #0]
  [cutsat] Assignment satisfying linear constraints
  [limits] Thresholds reached
    [limit] maximum term generation has been reached, threshold: `(gen := 8)`

[grind] Diagnostics
```
```leanOutput ematchUnbounded2 (expandTrace := limits) (expandTrace := ematch) (expandTrace := facts)
`grind` failed
case grind
h : s 0 = 0
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] s 0 = 0
    [prop] s 0 = s 1
    [prop] s 1 = s 2
    [prop] s 2 = s 3
    [prop] s 3 = s 4
    [prop] s 4 = s 5
    [prop] s 5 = s 6
    [prop] s 6 = s 7
    [prop] s 7 = s 8
  [eqc] Equivalence classes
  [ematch] E-matching patterns
    [thm] s_eq: [s #0]
  [cutsat] Assignment satisfying linear constraints
  [limits] Thresholds reached
    [limit] maximum term generation has been reached, threshold: `(gen := 8)`

[grind] Diagnostics
```
```lean
def iota : Nat → List Nat
  | 0 => []
  | n + 1 => n :: iota n

@[grind =] theorem iota_succ : iota (n + 1) = n :: iota n :=
  rfl
```
```lean +error (name := biggerGrindLimits)
example : (iota 20).length > 10 := by
  grind
```
```leanOutput biggerGrindLimits (expandTrace := limits) (expandTrace := facts)
`grind` failed
case grind
h : (iota 20).length ≤ 10
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] (iota 20).length ≤ 10
    [prop] iota 20 = 19 :: iota 19
    [prop] iota 19 = 18 :: iota 18
    [prop] (19 :: iota 19).length = (iota 19).length + 1
    [prop] iota 18 = 17 :: iota 17
    [prop] (18 :: iota 18).length = (iota 18).length + 1
    [prop] iota 17 = 16 :: iota 16
    [prop] (17 :: iota 17).length = (iota 17).length + 1
    [prop] iota 16 = 15 :: iota 15
    [prop] (16 :: iota 16).length = (iota 16).length + 1
  [eqc] True propositions
  [eqc] Equivalence classes
  [ematch] E-matching patterns
  [cutsat] Assignment satisfying linear constraints
  [ring] Ring `Lean.Grind.Ring.OfSemiring.Q Nat`
  [limits] Thresholds reached
    [limit] maximum number of E-matching rounds has been reached, threshold: `(ematch := 5)`

[grind] Diagnostics
```
```leanOutput biggerGrindLimits (expandTrace := limits) (expandTrace := facts)
`grind` failed
case grind
h : (iota 20).length ≤ 10
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] (iota 20).length ≤ 10
    [prop] iota 20 = 19 :: iota 19
    [prop] iota 19 = 18 :: iota 18
    [prop] (19 :: iota 19).length = (iota 19).length + 1
    [prop] iota 18 = 17 :: iota 17
    [prop] (18 :: iota 18).length = (iota 18).length + 1
    [prop] iota 17 = 16 :: iota 16
    [prop] (17 :: iota 17).length = (iota 17).length + 1
    [prop] iota 16 = 15 :: iota 15
    [prop] (16 :: iota 16).length = (iota 16).length + 1
  [eqc] True propositions
  [eqc] Equivalence classes
  [ematch] E-matching patterns
  [cutsat] Assignment satisfying linear constraints
  [ring] Ring `Lean.Grind.Ring.OfSemiring.Q Nat`
  [limits] Thresholds reached
    [limit] maximum number of E-matching rounds has been reached, threshold: `(ematch := 5)`

[grind] Diagnostics
```
```lean
example : (iota 20).length > 10 := by
  grind (gen := 20) (ematch := 20)
```
```lean (name := grindDiagnostics)
set_option diagnostics true in
example : (iota 20).length > 10 := by
  grind (gen := 20) (ematch := 20)
```
```leanOutput grindDiagnostics (expandTrace := grind) (expandTrace := thm)
[grind] Diagnostics
  [thm] E-Matching instances
    [thm] iota_succ ↦ 14
    [thm] List.length_cons ↦ 11
  [app] Applications
```
```leanOutput grindDiagnostics (expandTrace := grind) (expandTrace := thm)
[grind] Diagnostics
  [thm] E-Matching instances
    [thm] iota_succ ↦ 14
    [thm] List.length_cons ↦ 11
  [app] Applications
```
```lean (name := gt1diag)
theorem gt1 (x y : Nat) :
    x = y + 1 →
    0 < match x with
        | 0 => 0
        | _ + 1 => 1 := by
  set_option diagnostics true in
  grind
```
```leanOutput gt1diag (expandTrace := grind) (expandTrace := thm)
[grind] Diagnostics
  [thm] E-Matching instances
    [thm] gt1.match_1.congr_eq_2 ↦ 1
  [app] Applications
```
```leanOutput gt1diag (expandTrace := grind) (expandTrace := thm)
[grind] Diagnostics
  [thm] E-Matching instances
    [thm] gt1.match_1.congr_eq_2 ↦ 1
  [app] Applications
```
```lean (name := gt1matchtype)
#check gt1.match_1.congr_eq_2
```
```leanOutput gt1matchtype
gt1.match_1.congr_eq_2.{u_1} (motive : Nat → Sort u_1) (x✝ : Nat) (h_1 : Unit → motive 0)
  (h_2 : (n : Nat) → motive n.succ) (n✝ : Nat) (heq_1 : x✝ = n✝.succ) :
  (match x✝ with
    | 0 => h_1 ()
    | n.succ => h_2 n) ≍
    h_2 n✝
```
```leanOutput gt1matchtype
gt1.match_1.congr_eq_2.{u_1} (motive : Nat → Sort u_1) (x✝ : Nat) (h_1 : Unit → motive 0)
  (h_2 : (n : Nat) → motive n.succ) (n✝ : Nat) (heq_1 : x✝ = n✝.succ) :
  (match x✝ with
    | 0 => h_1 ()
    | n.succ => h_2 n) ≍
    h_2 n✝
```
```lean +error (name := noMatchEqs)
example (x y : Nat)
    : x = y + 1 →
      0 < match x with
          | 0 => 0
          | _+1 => 1 := by
  grind -matchEqs
```
```leanOutput noMatchEqs
`grind` failed
case grind.2
x y : Nat
h : x = y + 1
h_1 : (match x with
  | 0 => 0
  | n.succ => 1) =
  0
n : Nat
h_2 : x = n + 1
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] Equivalence classes
  [cases] Case analyses
  [cutsat] Assignment satisfying linear constraints
  [ring] Ring `Lean.Grind.Ring.OfSemiring.Q Nat`
```
```leanOutput noMatchEqs
`grind` failed
case grind.2
x y : Nat
h : x = y + 1
h_1 : (match x with
  | 0 => 0
  | n.succ => 1) =
  0
n : Nat
h_2 : x = n + 1
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] Equivalence classes
  [cases] Case analyses
  [cutsat] Assignment satisfying linear constraints
  [ring] Ring `Lean.Grind.Ring.OfSemiring.Q Nat`
```