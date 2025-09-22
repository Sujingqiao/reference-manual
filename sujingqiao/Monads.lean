```lean -show
section Laws
universe u u' v
axiom f : Type u → Type v
axiom m : Type u → Type v
variable [Functor f]
variable [Applicative f]
variable [Monad m]
axiom α : Type u'
axiom β : Type u'
axiom γ : Type u'
axiom x : f α
```
```lean -show
section F
variable {f : Type u → Type v} [Functor f] {α β : Type u} {g : α → β} {h : β → γ} {x : f α}
```
```lean -show
end F
``````lean -show
variable {m m' n : Type u → Type v} [Monad m] [Monad m'] [Monad n] [MonadLift m n]
variable {α β : Type u}
```
```lean -show
section
variable {m : Type → Type u}
```
```lean -show
end
```
```lean
def fromBaseIO (act : BaseIO α) : IO α := act
```
```lean (name := fromBase)
#check fun {α} (act : BaseIO α) => (act : IO α)
```
```leanOutput fromBase
fun {α} act => liftM act : {α : Type} → BaseIO α → EIO IO.Error α
```
```leanOutput fromBase
fun {α} act => liftM act : {α : Type} → BaseIO α → EIO IO.Error α
```
```lean -keep
def incrBy (n : Nat) : StateM Nat Unit := modify (· + n)

def incrOrFail : ReaderT Nat (ExceptT String (StateM Nat)) Unit := do
  if (← read) > 5 then throw "Too much!"
  incrBy (← read)
```
```lean (name := noLift) +error
set_option autoLift false

def incrBy (n : Nat) : StateM Nat Unit := modify (. + n)

def incrOrFail : ReaderT Nat (ExceptT String (StateM Nat)) Unit := do
  if (← read) > 5 then throw "Too much!"
  incrBy (← read)
```
```leanOutput noLift
Type mismatch
  incrBy __do_lift✝
has type
  StateM Nat Unit
but is expected to have type
  ReaderT Nat (ExceptT String (StateM Nat)) Unit
```
```leanOutput noLift
Type mismatch
  incrBy __do_lift✝
has type
  StateM Nat Unit
but is expected to have type
  ReaderT Nat (ExceptT String (StateM Nat)) Unit
```
```lean -show
variable {m n : Type u → Type v} {α ε : Type u}
```
```lean
set_option autoLift false

def getByte (n : Nat) : Except String UInt8 :=
  if n < 256 then
    pure n.toUInt8
  else throw s!"Out of range: {n}"

def getBytes (input : Array Nat) :
    StateT (Array UInt8) (Except String) Unit := do
  input.forM fun i =>
    liftM (Except.tryCatch (some <$> getByte i) fun _ => pure none) >>=
      fun
        | some b => modify (·.push b)
        | none => pure ()
```
```lean (name := getBytesEval1)
#eval getBytes #[1, 58, 255, 300, 2, 1000000] |>.run #[] |>.map (·.2)
```
```leanOutput getBytesEval1
Except.ok #[1, 58, 255, 2]
```
```leanOutput getBytesEval1
Except.ok #[1, 58, 255, 2]
```
```lean +error (name := getBytesErr) -keep
def getBytes' (input : Array Nat) :
    StateT (Array String)
      (StateT (Array UInt8)
        (Except String)) Unit := do
  input.forM fun i =>
    liftM
      (Except.tryCatch
        (getByte i >>= fun b =>
         modifyThe (Array UInt8) (·.push b))
        fun e =>
          modifyThe (Array String) (·.push e))
```
```leanOutput getBytesErr
failed to synthesize
  MonadStateOf (Array String) (Except String)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```
```leanOutput getBytesErr
failed to synthesize
  MonadStateOf (Array String) (Except String)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```
```lean
def getBytes' (input : Array Nat) :
    StateT (Array String)
      (StateT (Array UInt8)
        (Except String)) Unit := do
  input.forM fun i =>
    control fun run =>
      (Except.tryCatch
        (getByte i >>= fun b =>
         run (modifyThe (Array UInt8) (·.push b))))
        fun e =>
          run (modifyThe (Array String) (·.push e))
```
```lean (name := getBytesEval2)
#eval
  getBytes' #[1, 58, 255, 300, 2, 1000000]
  |>.run #[] |>.run #[]
  |>.map (fun (((), bytes), errs) => (bytes, errs))
```
```leanOutput getBytesEval2
Except.ok (#["Out of range: 300", "Out of range: 1000000"], #[1, 58, 255, 2])
```
```leanOutput getBytesEval2
Except.ok (#["Out of range: 300", "Out of range: 1000000"], #[1, 58, 255, 2])
``````lean -show
section FOps
variable {f : Type u → Type v} [Functor f] {α β : Type u} {g : α → β} {x : f α}
```
```lean -show
example : g <$> x = Functor.map g x := by rfl
example : x <&> g = Functor.map g x := by rfl
end FOps
```
```lean -show
section AOps
variable {f : Type u → Type v} [Applicative f] [Alternative f] {α β : Type u} {g : f (α → β)} {x e1 e e' : f α} {e2 : f β}
```
```lean -show
example : g <*> x = Seq.seq g (fun () => x) := by rfl
example : e1 *> e2 = SeqRight.seqRight e1 (fun () => e2) := by rfl
example : e1 <* e2 = SeqLeft.seqLeft e1 (fun () => e2) := by rfl
example : (e <|> e') = (OrElse.orElse e (fun () => e')) := by rfl
end AOps
```
```lean
structure User where
  name : String
  favoriteNat : Nat
def main : IO Unit := pure ()
```
```lean -show
section MOps
variable {m : Type u → Type v} [Monad m] {α β : Type u} {act : m α} {f : α → m β} {g : β → m γ}
```
```lean -show
example : act >>= f = Bind.bind act f := by rfl
example : f =<< act = Bind.bind act f := rfl
example : f >=> g = Bind.kleisliRight f g := by rfl
example : g <=< f = Bind.kleisliLeft g f := by rfl
end MOps
```
```lean -show
section
variable {m : Type → Type} [Monad m] {α β γ: Type} {e1 : m Unit} {e : β} {es : m α}
```
```leanTerm
    do
    e1
    es
    ```
```leanTerm
    e1 >>= fun () => do es
    ```
```lean -show -keep
def ex1a := do e1; es
def ex1b := e1 >>= fun () => do es
example : @ex1a = @ex1b := by rfl
```
```lean -show
section
variable {e1 : m β} {e1? : m (Option β)} {fallback : m α} {e2 : m γ} {f : β → γ → m Unit} {g : γ → α} {h : β → m γ}
```
```leanTerm
    do
    let x ← e1
    es
    ```
```leanTerm
    e1 >>= fun x =>
      do es
    ```
```leanTerm
    do
    let some x ← e1?
      | fallback
    es
    ```
```leanTerm
    e1? >>= fun
      | some x => do
        es
      | _ => fallback
    ```
```leanTerm
    do
    let x := e
    es
    ```
```leanTerm
    let x := e
    do es
    ```
```lean -show -keep
-- Test desugarings
def ex1a := do
    let x ← e1
    es
def ex1b :=
    e1 >>= fun x =>
      do es
example : @ex1a = @ex1b := by rfl


def ex2a :=
    do
    let some x ← e1?
      | fallback
    es

def ex2b :=
    e1? >>= fun
      | some x => do
        es
      | _ => fallback
example : @ex2a = @ex2b := by rfl

def ex3a :=
    do
    let x := e
    es
def ex3b :=
    let x := e
    do es
example : @ex3a = @ex3b := by rfl
```
```leanTerm
    do
    f (← e1) (← e2)
    es
    ```
```leanTerm
    do
    let x ← e1
    let y ← e2
    f x y
    es
    ```
```leanTerm
    do
    let x := g (← h (← e1))
    es
    ```
```leanTerm
    do
    let y ← e1
    let z ← h y
    let x := g z
    es
    ```
```lean -show -keep
-- Test desugarings
def ex1a := do
  f (← e1) (← e2)
  es
def ex1b := do
  let x ← e1
  let y ← e2
  f x y
  es
example : @ex1a = @ex1b := by rfl
def ex2a := do
  let x := g (← h (← e1))
  es
def ex2b := do
  let y ← e1
  let z ← h y
  let x := g z
  es
example : @ex2a = @ex2b := by rfl
```
```lean (name := earlyStop)
#eval Id.run do
  let mut v := #[]
  for x in [0:43], y in ['a', 'b'] do
    v := v.push (x, y)
  return v
```
```leanOutput earlyStop
#[(0, 'a'), (1, 'b')]
```
```leanOutput earlyStop
#[(0, 'a'), (1, 'b')]
```
```lean -keep
def satisfyingIndices
    (p : α → Prop) [DecidablePred p]
    (xs : Array α) : Array Nat := Id.run do
  let mut out := #[]
  for h : i in [0:xs.size] do
    if p xs[i] then out := out.push i
  return out
```
```lean -keep -show
-- test it
/--
error: failed to prove index is valid, possible solutions:
  - Use `have`-expressions to prove the index is valid
  - Use `a[i]!` notation instead, runtime check is performed, and 'Panic' error message is produced if index is not valid
  - Use `a[i]?` notation instead, result is an `Option` type
  - Use `a[i]'h` notation instead, where `h` is a proof that index is valid
m : Type → Type
inst✝¹ : Monad m
α β γ : Type
e1✝ : m Unit
e : β
es : m α
e1 : m β
e1? : m (Option β)
fallback : m α
e2 : m γ
f : β → γ → m Unit
g : γ → α
h : β → m γ
p : α → Prop
inst✝ : DecidablePred p
xs : Array α
out✝ : Array Nat := #[]
i : Nat
r✝ : Array Nat
out : Array Nat := r✝
⊢ i < xs.size
-/
#check_msgs in
def satisfyingIndices (p : α → Prop) [DecidablePred p] (xs : Array α) : Array Nat := Id.run do
  let mut out := #[]
  for i in [0:xs.size] do
    if p xs[i] then out := out.push i
  return out
```
```lean -show
axiom «<B>» : Type u
axiom «<b>» : β
variable [Monad m] (xs : Coll) [ForIn m Coll α] [instMem : Membership α Coll] [ForIn' m Coll α instMem]
variable (f : α → β → m β) (f' : (x : α) → x ∈ xs → β → m β)

macro "…" : term => `((«<b>» : β))
```
```leanTerm (type := "m α")
    do
    let mut b := …
    for x in xs do
      b ← f x b
    es
    ```
```leanTerm (type := "m α")
    do
    let b := …
    let b ← ForIn.forIn xs b fun x b => do
      let b ← f x b
      return ForInStep.yield b
    es
    ```
```leanTerm (type := "m α")
    do
    let mut b := …
    for x in xs do
      b ← f x b
      break
    es
    ```
```leanTerm (type := "m α")
    do
    let b := …
    let b ← ForIn.forIn xs b fun x b => do
      let b ← f x b
      return ForInStep.done b
    es
    ```
```leanTerm (type := "m α")
    do
    let mut b := …
    for h : x in xs do
      b ← f' x h b
    es
    ```
```leanTerm (type := "m α")
    do
    let b := …
    let b ← ForIn'.forIn' xs b fun x h b => do
      let b ← f' x h b
      return ForInStep.yield b
    es
    ```
```leanTerm (type := "m α")
    do
    let mut b := …
    for h : x in xs do
      b ← f' x h b
      break
    es
    ```
```leanTerm (type := "m α")
    do
    let b := …
    let b ← ForIn'.forIn' xs b fun x h b => do
      let b ← f' x h b
      return ForInStep.done b
    es
    ```
```lean (name := natBreak)
#eval show Option Nat from do
  let mut i := 0
  repeat
    if i > 1000 then failure
    else i := 2 * (i + 1)
  return i
```
```leanOutput natBreak
none
```
```leanOutput natBreak
none
```
```lean -show
-- Test nested `do` rules

/-- info: ((), 6) -/
#check_msgs in
#eval (·.run 0) <| show StateM Nat Unit from do
  set 5
  do
    set 6
    return

/-- error: must be last element in a `do` sequence -/
#check_msgs in
#eval (·.run 0) <| show StateM Nat Unit from do
  set 5
  do
    set 6
    return
  set 7
  return

/-- info: ((), 6) -/
#check_msgs in
#eval (·.run 0) <| show StateM Nat Unit from do
  set 5
  if true then
    set 6
    do return
  set 7
  return
```
```lean (name := nestedDo)
def test : StateM Nat Unit := do
  set 5
  if true then
    set 6
    do return
  set 7
  return

#eval test.run 0
```
```leanOutput nestedDo
((), 6)
```
```leanOutput nestedDo
((), 6)
```
```lean -show
end
```
```lean -show
-- tests for this section
set_option pp.all true

/--
info: @Bind.bind.{0, 0} m (@Monad.toBind.{0, 0} m inst✝) Unit α e1 fun (x : PUnit.{1}) => es : m α
-/
#check_msgs in
#check do e1; es

section
variable {e1 : m β}
/-- info: @Bind.bind.{0, 0} m (@Monad.toBind.{0, 0} m inst✝) β α e1 fun (x : β) => es : m α -/
#check_msgs in
#check do let x ← e1; es
end

/--
info: let x : β := e;
es : m α
-/
#check_msgs in
#check do let x := e; es

variable {e1 : m β} {e2 : m γ} {f : β → γ → m Unit} {g : γ → α} {h : β → m γ}

/--
info: @Bind.bind.{0, 0} m (@Monad.toBind.{0, 0} m inst✝) β α e1 fun (__do_lift : β) =>
  @Bind.bind.{0, 0} m (@Monad.toBind.{0, 0} m inst✝) γ α e2 fun (__do_lift_1 : γ) =>
    @Bind.bind.{0, 0} m (@Monad.toBind.{0, 0} m inst✝) Unit α (f __do_lift __do_lift_1) fun (x : PUnit.{1}) => es : m α
-/
#check_msgs in
#check do f (← e1) (← e2); es

/--
info: @Bind.bind.{0, 0} m (@Monad.toBind.{0, 0} m inst✝) β α e1 fun (__do_lift : β) =>
  @Bind.bind.{0, 0} m (@Monad.toBind.{0, 0} m inst✝) γ α (h __do_lift) fun (__do_lift : γ) =>
    let x : α := g __do_lift;
    es : m α
-/
#check_msgs in
#check do let x := g (← h (← e1)); es

end


``````lean
def sumNonFives {m}
    [Monad m] [MonadState Nat m] [MonadExcept String m]
    (xs : List Nat) :
    m Unit := do
  for x in xs do
    if x == 5 then
      throw "Five was encountered"
    else
      modify (· + x)
```
```lean (name := exSt)
#eval
  sumNonFives (m := ExceptT String (StateM Nat))
    [1, 2, 3, 4, 5, 6] |>.run |>.run 0
```
```leanOutput exSt
(Except.error "Five was encountered", 10)
```
```leanOutput exSt
(Except.error "Five was encountered", 10)
```
```lean (name := stEx)
#eval
  sumNonFives (m := StateT Nat (Except String))
    [1, 2, 3, 4, 5, 6] |>.run 0
```
```leanOutput stEx
Except.error "Five was encountered"
```
```leanOutput stEx
Except.error "Five was encountered"
```
```lean
/-- Computes the sum of the non-5 prefix of a list. -/
def sumUntilFive {m}
    [Monad m] [MonadState Nat m] [MonadExcept String m]
    (xs : List Nat) :
    m Nat := do
  MonadState.set 0
  try
    sumNonFives xs
  catch _ =>
    pure ()
  get
```
```lean (name := exSt2)
#eval
  sumUntilFive (m := ExceptT String (StateM Nat))
    [1, 2, 3, 4, 5, 6] |>.run |>.run' 0
```
```leanOutput exSt2
Except.ok 10
```
```leanOutput exSt2
Except.ok 10
```
```lean (name := stEx2)
#eval
  sumUntilFive (m := StateT Nat (Except String))
    [1, 2, 3, 4, 5, 6] |>.run' 0
```
```leanOutput stEx2
Except.ok 0
```
```leanOutput stEx2
Except.ok 0
```
```lean -show
example : @get = @MonadState.get := by rfl
example : @set = @MonadStateOf.set := by rfl
example {inst} (f : σ → σ) : @modify σ m inst f = @MonadState.modifyGet σ m inst PUnit fun (s : σ) => (PUnit.unit, f s) := by rfl
example : @modifyGet = @MonadState.modifyGet := by rfl
example : @read = @MonadReader.read := by rfl
example : @readThe = @MonadReaderOf.read := by rfl
example : @withReader = @MonadWithReader.withReader := by rfl
example : @withTheReader = @MonadWithReaderOf.withReader := by rfl
example : @throw = @MonadExcept.throw := by rfl
example : @throwThe = @MonadExceptOf.throw := by rfl
example : @tryCatch = @MonadExcept.tryCatch := by rfl
example : @tryCatchThe = @MonadExceptOf.tryCatch := by rfl
```
```lean
abbrev M := StateT Nat (StateM String)
```
```lean (name := getM)
#check (get : M _)
```
```leanOutput getM
get : M Nat
```
```leanOutput getM
get : M Nat
```
```lean (name := getMStr) +error
#check (get : M String)
```
```leanOutput getMStr
failed to synthesize
  MonadState String M

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```
```leanOutput getMStr
failed to synthesize
  MonadState String M

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```
```lean (name := getTheM)
#check ((getThe String, getThe Nat) : M String × M Nat)
```
```leanOutput getTheM
(getThe String, getThe Nat) : M String × M Nat
```
```leanOutput getTheM
(getThe String, getThe Nat) : M String × M Nat
```
```lean (name := setNat)
#check (set 4 : M Unit)
```
```leanOutput setNat
set 4 : M PUnit
```
```leanOutput setNat
set 4 : M PUnit
```
```lean (name := setStr)
#check (set "Four" : M Unit)
```
```leanOutput setStr
set "Four" : M PUnit
```
```leanOutput setStr
set "Four" : M PUnit
```
```lean -show
variable {α : Type u} (T : (Type u → Type v) → Type u → Type w) (m : Type u → Type v)

```
```lean -show
universe u v
variable {m : Type u → Type v} {α : Type u}
```
```lean
def IdT (m : Type u → Type v) : Type u → Type v := m
```
```lean
def IdT.run (act : IdT m α) : m α := act
```
```lean
instance [Monad m] : Monad (IdT m) where
  pure x := (pure x : m _)
  bind x f := (x >>= f : m _)
```
```lean
instance : MonadLift m (IdT m) where
  monadLift x := x
```
```lean
instance [Monad m] : MonadControl m (IdT m) where
  stM α := α
  liftWith f := f (fun x => Id.run <| pure x)
  restoreM v := v
``````lean -show
variable (ε : Type u) (σ σ' : Type u) (α : Type u)
```
```lean -show
/-- info: σ → Except ε α × σ -/
#check_msgs in
#reduce (types := true) ExceptT ε (StateM σ) α

/-- info: σ → EStateM.Result ε σ α -/
#check_msgs in
#reduce (types := true) EStateM ε σ α
``````lean -show
universe u
variable (α : Type u)
variable (ε : Type u)
variable {m : Type u → Type v}
```
```lean -show
/-- info: (β : Type u) → (α → m β) → (ε → m β) → m β -/
#check_msgs in
#reduce (types := true) ExceptCpsT ε m α
``````lean -show
-- Verify claims
example : Id = id := rfl
example : Id.run (α := α) = id := rfl
example : (pure (f := Id)) = (id : α → α) := rfl
example : (bind (m := Id)) = (fun (x : α) (f : α → Id β) => f x) := rfl
```
```lean (name := idDo)
#eval Id.run do
  let mut xs := []
  for x in [0:10] do
    xs := x :: xs
  pure xs
```
```leanOutput idDo
[9, 8, 7, 6, 5, 4, 3, 2, 1, 0]
```
```leanOutput idDo
[9, 8, 7, 6, 5, 4, 3, 2, 1, 0]
``````lean -show
variable {α σ : Type u}
```
```lean -show
/-- info: (δ : Type u) → σ → (α → σ → Id δ) → δ -/
#check_msgs in
#reduce (types := true) StateCpsT σ Id α
```
```lean -show
variable {m : Type → Type} {σ ω : Type} [STWorld σ m]
```