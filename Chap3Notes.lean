import HTPILib.HTPIDefs
namespace HTPI

example (U: Type) (P Q : Pred U)
  (h1: ∀ (x: U), P x → ¬Q x)
  (h2: ∀ (x: U), Q x) :
  ¬∃(x: U), P x := by
  quant_neg
  fix y: U
  have h3: P y → ¬Q y := h1 y
  have h4: Q y := h2 y
  contrapos at h3
  show ¬P y from h3 h4


example (U : Type) (A B C : Set U)
    (h1 : A ⊆ B ∪ C)
    (h2 : ∀ (x : U), x ∈ A → x ∉ B) : A ⊆ C := by
    define
    fix y: U
    assume h3: y ∈ A
    have h4: y ∉ B := h2 y h3
    define at h1
    have h5: y ∈ B ∪ C := h1 h3
    define at h5
    conditional at h5
    show y ∈ C from h5 h4


example (U : Type) (P Q : Pred U)
    (h1 : ∀ (x : U), ∃ (y : U), P x → ¬ Q y)
    (h2: ∃ (x : U), ∀ (y : U), P x → Q y) :
    ∃ (x : U), ¬P x := by
    obtain (a : U) (h3 : ∀ (y : U), P a → Q y) from h2
    have h4: ∃ (y : U), P a → ¬Q y := h1 a
    obtain (b : U) (h5: P a → ¬Q b) from h4
    have h6: P a → Q b := h3 b
    apply Exists.intro a _
    by_contra h7
    show False from (h5 h7) (h6 h7)
