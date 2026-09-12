namespace DimensionalKonstruktor

universe u v w x

/-- A semantic kernel program is just a total map between semantic domains. -/
abbrev Prog (α : Type u) (β : Type v) := α → β

namespace Prog

protected def id : Prog α α := fun x => x

def comp (g : Prog β γ) (f : Prog α β) : Prog α γ :=
  fun x => g (f x)

@[simp] theorem comp_id_left (f : Prog α β) :
    comp Prog.id f = f := by
  funext x
  rfl

@[simp] theorem comp_id_right (f : Prog α β) :
    comp f Prog.id = f := by
  funext x
  rfl

@[simp] theorem comp_assoc
    (f : Prog α β) (g : Prog β γ) (h : Prog γ δ) :
    comp h (comp g f) = comp (comp h g) f := by
  funext x
  rfl

end Prog

/-- Pull a field back through a chart/generator map Γ. -/
def pullback (γ : Q → Q) (field : Q → V) : Q → V :=
  fun q => field (γ q)

/-- Γ composition has the expected contravariant action on fields. -/
theorem pullback_comp
    (γ₁ γ₂ : Q → Q) (field : Q → V) :
    pullback (Prog.comp γ₂ γ₁) field =
      pullback γ₁ (pullback γ₂ field) := by
  funext q
  rfl

/-- A cut/event surface chooses one of two local semantic programs. -/
def cut (side : Q → Bool) (a b : Q → V) : Q → V :=
  fun q => if side q then a q else b q

@[simp] theorem cut_true
    (side : Q → Bool) (a b : Q → V) (q : Q)
    (h : side q = true) :
    cut side a b q = a q := by
  simp [cut, h]

@[simp] theorem cut_false
    (side : Q → Bool) (a b : Q → V) (q : Q)
    (h : side q = false) :
    cut side a b q = b q := by
  simp [cut, h]

/-- Semantic property carried by a certified endomorphism. -/
def Preserves (I : α → Prop) (f : α → α) : Prop :=
  ∀ x, I x → I (f x)

theorem preserves_id (I : α → Prop) :
    Preserves I (fun x => x) := by
  intro x hx
  exact hx

theorem preserves_comp
    (I : α → Prop) (f g : α → α)
    (hf : Preserves I f) (hg : Preserves I g) :
    Preserves I (Prog.comp g f) := by
  intro x hx
  exact hg (f x) (hf x hx)

/-- Certification-first operator: its semantic action and proof travel together. -/
structure CertifiedEndo (α : Type u) (I : α → Prop) where
  run : α → α
  preserves : Preserves I run

namespace CertifiedEndo

def id (I : α → Prop) : CertifiedEndo α I where
  run := fun x => x
  preserves := preserves_id I

def comp
    (g f : CertifiedEndo α I) : CertifiedEndo α I where
  run := Prog.comp g.run f.run
  preserves := preserves_comp I f.run g.run f.preserves g.preserves

@[simp] theorem comp_run
    (g f : CertifiedEndo α I) (x : α) :
    (comp g f).run x = g.run (f.run x) := by
  rfl

end CertifiedEndo

/-!
A tiny kernel AST and a deliberately distinct lowering target.  The target
records precomposition and cuts as executable nodes.  `lower_correct` proves
that lowering preserves denotational semantics for every expression.
-/

inductive KExpr (Q : Type u) (V : Type v) where
  | atom : (Q → V) → KExpr Q V
  | gamma : (Q → Q) → KExpr Q V → KExpr Q V
  | cut : (Q → Bool) → KExpr Q V → KExpr Q V → KExpr Q V

namespace KExpr

def eval : KExpr Q V → Q → V
  | atom f => f
  | gamma γ e => fun q => eval e (γ q)
  | cut side a b => fun q => if side q then eval a q else eval b q

end KExpr

inductive LExpr (Q : Type u) (V : Type v) where
  | leaf : (Q → V) → LExpr Q V
  | mapInput : (Q → Q) → LExpr Q V → LExpr Q V
  | branch : (Q → Bool) → LExpr Q V → LExpr Q V → LExpr Q V

namespace LExpr

def exec : LExpr Q V → Q → V
  | leaf f => f
  | mapInput γ e => fun q => exec e (γ q)
  | branch side a b => fun q => if side q then exec a q else exec b q

end LExpr

def lower : KExpr Q V → LExpr Q V
  | .atom f => .leaf f
  | .gamma γ e => .mapInput γ (lower e)
  | .cut side a b => .branch side (lower a) (lower b)

/-- The first nontrivial compiler theorem: this lowering is semantics preserving. -/
theorem lower_correct (e : KExpr Q V) :
    LExpr.exec (lower e) = KExpr.eval e := by
  funext q
  induction e generalizing q with
  | atom f =>
      rfl
  | gamma γ e ih =>
      exact ih (q := γ q)
  | cut side a b iha ihb =>
      simp only [lower, LExpr.exec, KExpr.eval]
      by_cases h : side q = true
      · simp [h, iha, ihb]
      · have hf : side q = false := by
          cases hs : side q <;> simp_all
        simp [hf, iha, ihb]

/-- Pointwise form, useful as an executable oracle contract. -/
theorem lower_correct_at (e : KExpr Q V) (q : Q) :
    LExpr.exec (lower e) q = KExpr.eval e q := by
  simpa using congrFun (lower_correct e) q

end DimensionalKonstruktor
