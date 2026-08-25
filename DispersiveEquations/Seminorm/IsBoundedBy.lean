/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.LocallyConvex.WithSeminorms

/-! # Boundedness of seminorms -/

@[expose] public noncomputable section


open NormedField Set Seminorm TopologicalSpace Filter List Bornology

open NNReal Pointwise Topology Uniformity

variable {𝕜 𝕜₁ 𝕜₂ 𝕜₁' 𝕜₂' E E₁ E₂ Eₗ F F₁ F₂ ι ι' : Type*}

section WithSeminormsEmbedding

variable [NormedField 𝕜₁] [NormedField 𝕜₂]
  {σ₁₂ : 𝕜₁ →+* 𝕜₂} [RingHomIsometric σ₁₂]
  [AddCommGroup E₁] [Module 𝕜₁ E₁] [AddCommGroup E₂] [Module 𝕜₂ E₂]

namespace Seminorm

/-- A seminorm `p` is bounded by another seminorm `q` if there exists `C : ℝ≥0` such that
`p ≤ C • q`. -/
def IsBoundedBy (p q : Seminorm 𝕜₁ E₁) : Prop :=
  ∃ (C : ℝ≥0), p ≤ C • q

/-- Two seminorms `p, q` are equivalent if `p` is bounded by `q` and `q` is bounded by `p`. -/
def IsEquivalent (p q : Seminorm 𝕜₁ E₁) : Prop :=
  ∃ (C : ℝ≥0), p ≤ C • q ∧ q ≤ C • p

variable {p p' q q' : Seminorm 𝕜₁ E₁}

theorem isBoundedBy_iff (p q : Seminorm 𝕜₁ E₁) :
    p.IsBoundedBy q ↔ ∃ (C : ℝ≥0), p ≤ C • q := by rfl

/-- A seminorm `p` is bounded by another seminorm `q` if and only if there exists `C : ℝ` such that
for all `x`, `p x ≤ C * q x`. -/
@[grind =]
theorem isBoundedBy_iff_forall (p q : Seminorm 𝕜₁ E₁) :
    p.IsBoundedBy q ↔ ∃ C, ∀ x, p x ≤ C * q x := by
  rw [isBoundedBy_iff]
  constructor
  · intro ⟨C, h⟩
    use C
    intro x
    rw [Seminorm.le_def] at h
    grw [h x]
    norm_cast
  · intro ⟨C, h⟩
    use C.toNNReal
    rw [Seminorm.le_def]
    intro x
    grw [h x]
    suffices C • q x ≤ (C.toNNReal : ℝ) • q x by simpa using! this
    gcongr
    simp

variable {R : Type*} [SMul R ℝ] [SMul R ℝ≥0] [IsScalarTower R ℝ≥0 ℝ]
  [Preorder R] [Zero R] [IsOrderedModule R ℝ]

instance : IsOrderedSMul R (Seminorm 𝕜₁ E₁) where
  smul_le_smul_left p q hpq c := by
    rw [le_def] at hpq ⊢
    intro x
    simp only [smul_apply]
    have hp : (c • (1 : ℝ≥0)) • p x = c • p x := by simp
    have hq : (c • (1 : ℝ≥0)) • q x = c • q x := by simp
    grw [← hp, smul_le_smul_of_nonneg_left (hpq x) (by positivity), hq]
  smul_le_smul_right a b hab p := by
    rw [le_def]
    intro x
    simp only [smul_apply]
    grw [smul_le_smul_of_nonneg_right hab (by positivity)]

@[grind .]
theorem isBoundedBy_self (p : Seminorm 𝕜₁ E₁) : p.IsBoundedBy p := by
  use 1
  simp

@[grind →]
theorem IsBoundedBy.trans (h : p.IsBoundedBy q) (h' : q.IsBoundedBy q') :
    p.IsBoundedBy q' := by
  obtain ⟨C, h⟩ := h
  obtain ⟨C', h'⟩ := h'
  use C * C'
  grw [h, h']
  simp [← smul_assoc]

@[grind .]
theorem IsBoundedBy.smul_left (h : p.IsBoundedBy q) (a : R) : (a • p).IsBoundedBy q := by
  obtain ⟨C, h⟩ := h
  use a • C
  grw [h, smul_assoc]

@[grind ←]
theorem IsBoundedBy.smul_right (h : p.IsBoundedBy q) {a : ℝ≥0} (ha : a ≠ 0) :
    p.IsBoundedBy (a • q) := by
  obtain ⟨C, h⟩ := h
  use a⁻¹ • C
  calc
    _ ≤ C • q := h
    _ = _ := by
      rw [← smul_assoc]
      congr
      simp [field]

attribute [gcongr] IsOrderedSMul.smul_le_smul

@[grind .]
theorem IsBoundedBy.add (h : p.IsBoundedBy q) (h' : p'.IsBoundedBy q') :
    (p + p').IsBoundedBy (q + q') := by
  obtain ⟨C, h⟩ := h
  obtain ⟨C', h'⟩ := h'
  use max C C'
  calc
    _ ≤ C • q + C' • q' := by grw [h, h']
    _ ≤ max C C' • q + max C C' • q' := by
      gcongr
      all_goals simp
    _ = _ := by simp

instance : IsStrictOrderedModule ℕ ℝ where

@[grind .]
theorem IsBoundedBy.add_left (h : p.IsBoundedBy q) (h' : p'.IsBoundedBy q) :
    (p + p').IsBoundedBy q := by
  have h₁ : (p + p').IsBoundedBy (q + q) := h.add h'
  have h₂ : (2 • q).IsBoundedBy q := by grind
  grind [two_nsmul]

@[symm]
theorem IsEquivalent.symm (h : p.IsEquivalent q) : q.IsEquivalent p := by
  obtain ⟨C, h⟩ := h
  exact ⟨C, h.symm⟩

@[grind =]
theorem isEquivalent_comm (p q : Seminorm 𝕜₁ E₁) : p.IsEquivalent q ↔ q.IsEquivalent p :=
  ⟨(·.symm), (·.symm)⟩

@[grind =]
theorem isEquivalent_iff_isBoundedBy (p q : Seminorm 𝕜₁ E₁) :
    p.IsEquivalent q ↔ p.IsBoundedBy q ∧ q.IsBoundedBy p := by
  constructor
  · intro ⟨C, h₁, h₂⟩
    exact ⟨⟨C, h₁⟩, ⟨C, h₂⟩⟩
  · intro ⟨⟨C₁, h₁⟩, ⟨C₂, h₂⟩⟩
    use max C₁ C₂
    constructor
    · grw [h₁]
      gcongr
      simp
    · grw [h₂]
      gcongr
      simp

theorem isEquivalent_self (p : Seminorm 𝕜₁ E₁) : p.IsEquivalent p := by grind

end Seminorm
