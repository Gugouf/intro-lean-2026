/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Guilherme Lima
-/
module

/- Simple imperative programs -/

@[expose] public section

namespace Hello.Imp

/-! ## Abstract syntax -/

/-- Arithmetic expression. -/
inductive AExp where
  | num (n : Nat)
  | var (x : String)
  | add (a₁ a₂ : AExp)
  | sub (a₁ a₂ : AExp)
  | mul (a₁ a₂ : AExp)
deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr

/-- Boolean expression. -/
inductive BExp where
  | true
  | false
  | eq (a₁ a₂ : AExp)
  | ne (a₁ a₂ : AExp)
  | le (a₁ a₂ : AExp)
  | gt (a₁ a₂ : AExp)
  | not (b : BExp)
  | and (b₁ b₂ : BExp)
deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr

/-- Commands. -/
inductive Comm where
  | skip
  | assign (x : String) (a : AExp)
  | seq (c₁ c₂ : Comm)
  | ifelse (b : BExp) (c₁ c₂ : Comm)
  | while (b : BExp) (c : Comm)

/- Notations. -/
scoped infixr:70 " ≔ " => Comm.assign
scoped infixr:64 " ,, " => Comm.seq

/-! ## Semantics -/

/-- A "state" is a mapping of variable names to number values. -/
abbrev State := String → Nat

/-- The empty state. -/
def State.empty : State := fun _ ↦ 0

/-- Updates the state, associating name `x` to value `n`. -/
def State.update (s : State) (x : String) (n : Nat) : State :=
  fun y ↦ if y == x then n else s y

instance : Inhabited State where
  default := State.empty

/-- Semantics of arithmetic expressions. -/
def AExp.eval (s : State) : AExp → Nat
  | num n => n
  | var x => s x
  | add a₁ a₂ => a₁.eval s + a₂.eval s
  | sub a₁ a₂ => a₁.eval s - a₂.eval s
  | mul a₁ a₂ => a₁.eval s * a₂.eval s

/-- Semantics of boolean expressions. -/
def BExp.eval (s : State) : BExp → Bool
  | true => .true
  | false => .false
  | eq a₁ a₂ => a₁.eval s == a₂.eval s
  | ne a₁ a₂ => a₁.eval s != a₂.eval s
  | le a₁ a₂ => a₁.eval s ≤ a₂.eval s
  | gt a₁ a₂ => a₁.eval s > a₂.eval s
  | not b => !b.eval s
  | and b₁ b₂ => b₁.eval s && b₂.eval s

/-- Semantics of commands. -/
inductive Comm.eval : Comm → State → State → Prop where
  /-- Rule for `skip`. -/
  | eSkip (s : State) :
      skip.eval s s

  /-- Rule for `assign`. -/
  | eAssign (s : State) (a : AExp) (n : Nat) (x : String) :
      a.eval s = n →
      (assign x a).eval s (s.update x n)

  /-- Rule for `seq`. -/
  | eSeq (c₁ c₂ : Comm) (s₁ s₂ s₃ : State) :
      c₁.eval s₁ s₂ →
      c₂.eval s₂ s₃ →
      (c₁.seq c₂).eval s₁ s₃

  /-- Rule for `ifelse`, negative case. -/
  | eIfFalse (c₁ c₂ : Comm) (s₁ s₂ : State) (b : BExp) :
      ¬b.eval s₁ →
      c₂.eval s₁ s₂ →
      (ifelse b c₁ c₂).eval s₁ s₂

  /-- Rule for `ifelse`, positive case. -/
  | eIfTrue (c₁ c₂ : Comm) (s₁ s₂ : State) (b : BExp) :
      b.eval s₁ →
      c₁.eval s₁ s₂ →
      (ifelse b c₁ c₂).eval s₁ s₂

  /-- Rule for `while`, negative case. -/
  | eWhileFalse (c : Comm) (s : State) (b : BExp) :
      ¬b.eval s →
      (c.while b).eval s s

  /-- Rule for `while`, positive case. -/
  | eWhileTrue (c : Comm) (s₁ s₂ s₃ : State) (b : BExp) :
      b.eval s₁ →
      c.eval s₁ s₂ →
      (c.while b).eval s₂ s₃ →
      (c.while b).eval s₁ s₃

/--
The following program terminates in a state where "X" is 2 and "Z" is 4.
-/
example : (
    "X" ≔ .num 2 ,,
    .ifelse (BExp.le (.var "X") (.num 1))
      ("Y" ≔ .num 3)
      ("Z" ≔ .num 4)
    ).eval .empty ((State.empty.update "X" 2).update "Z" 4) := by
  apply Comm.eval.eSeq (s₂ := (State.empty.update "X" 2))
  · apply Comm.eval.eAssign; simp [AExp.eval]
  · apply Comm.eval.eIfFalse
    · simp [AExp.eval, BExp.eval, State.update]
    · apply Comm.eval.eAssign
      simp [AExp.eval]

/--
Command evaluation is deterministic.
The proof is by induction on command evaluation.
-/
theorem comm_eval_deterministic (c : Comm) (s s₁ s₂ : State) :
    c.eval s s₁ → c.eval s s₂ → s₁ = s₂ := by
  intro e₁
  induction e₁ generalizing s₂ with
  | eSkip => intro h; cases h; rfl
  | eAssign => intro h; cases h; simp_all
  | eSeq _ _ _ _ _ _ _ ih₁ ih₂ =>
    intro h; cases h with
    | eSeq _ _ _ _ _ h₁ h₂ =>
      have := ih₁ _ h₁; subst this; exact ih₂ _ h₂
  | eIfFalse _ _ _ _ _ _ _ ih =>
    intro h; apply ih; cases h with
    | eIfFalse => assumption
    | eIfTrue => contradiction
  | eIfTrue _ _ _ _ _ _ _ ih =>
    intro h; apply ih; cases h <;> simp_all
  | eWhileFalse =>
    intro h; cases h <;> simp_all
  | eWhileTrue _ _ _ _ _ _ _ _ ih₁ ih₂ =>
    intro h; cases h with
    | eWhileFalse => contradiction
    | eWhileTrue _ _ _ _ _ _ h₁ h₂ =>
      have := ih₁ _ h₁; subst this; exact ih₂ _ h₂

/-! ## Optimizations -/

/-- Replaces subexpressions of the form `add 0 a` by `a`. -/
def AExp.optZeroAdd : AExp → AExp
  | num n => num n
  | var x => var x
  | add (.num 0) a => a
  | add a₁ a₂ => add a₁.optZeroAdd a₂.optZeroAdd
  | sub a₁ a₂ => sub a₁.optZeroAdd a₂.optZeroAdd
  | mul a₁ a₂ => mul a₁.optZeroAdd a₂.optZeroAdd

/--
`optZeroAdd` is sound, i.e., preserves semantics.
The proof is by induction on the structure of arithmetic expressions.
-/
theorem optZeroAdd_sound (a : AExp) (s : State) :
    a.eval s = a.optZeroAdd.eval s := by
  fun_induction AExp.optZeroAdd <;> simp_all [AExp.eval]

end Hello.Imp
