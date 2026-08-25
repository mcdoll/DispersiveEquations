/-
Copyright (c) 2026 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
module

public import Mathlib.Analysis.Asymptotics.TVS
public import Mathlib.Analysis.LocallyConvex.WithSeminorms

/-!
# Asymptotics for locally convex topological vector spaces

mathlib PR #42676
-/

@[expose] public section

open scoped NNReal
open Filter

variable {ι κ α 𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]
  [AddCommGroup F] [TopologicalSpace F] [Module 𝕜 F]
variable {f f₁ f₂ : α → E} {g g₁ g₂ : α → F} {l : Filter α}
namespace PolynormableSpace

variable [PolynormableSpace 𝕜 E] [PolynormableSpace 𝕜 F]

theorem isBigOTVS_iff_le :
    f =O[𝕜; l] g ↔ ∀ p : Seminorm 𝕜 E, Continuous p → ∃ q : Seminorm 𝕜 F,
      Continuous q ∧ p ∘ f ≤ᶠ[l] q ∘ g := by sorry

theorem isBigOTVS_iff :
    f =O[𝕜; l] g ↔ ∀ p : Seminorm 𝕜 E, Continuous p → ∃ q : Seminorm 𝕜 F,
      Continuous q ∧ (p ∘ f) =O[l] (q ∘ g) := by
  simp_rw [isBigOTVS_iff_le, Filter.EventuallyLE]
  congrm ∀ p p_cont, ?_
  constructor <;> rintro ⟨q, q_cont, hq⟩
  · exact ⟨q, q_cont, .of_bound' <| by simpa (discharger := positivity) [abs_of_nonneg]⟩
  · rw [Asymptotics.isBigO_iff'] at hq
    rcases hq with ⟨C, C_pos, hC⟩
    simp (discharger := positivity) only [Function.comp_apply, Real.norm_of_nonneg] at hC
    refine ⟨C.toNNReal • q, q_cont.const_smul _, ?_⟩
    simpa [NNReal.smul_def, C_pos.le]

theorem isLittleOTVS_iff_le :
    f =o[𝕜; l] g ↔ ∀ p : Seminorm 𝕜 E, Continuous p → ∃ q : Seminorm 𝕜 F,
      Continuous q ∧ ∀ ε : ℝ≥0, ε ≠ 0 → p ∘ f ≤ᶠ[l] (ε • q) ∘ g := by sorry

theorem isLittleOTVS_iff :
    f =o[𝕜; l] g ↔ ∀ p : Seminorm 𝕜 E, Continuous p → ∃ q : Seminorm 𝕜 F,
      Continuous q ∧ (p ∘ f) =o[l] (q ∘ g) := by
  simp_rw [isLittleOTVS_iff_le, Filter.EventuallyLE, Asymptotics.isLittleO_iff]
  congrm ∀ p p_cont, ∃ q, _ ∧ ?_
  constructor <;> intro H ε hε
  · have : NNReal.mk ε hε.le ≠ 0 := by simpa [← NNReal.coe_ne_zero] using hε.ne'
    simpa (discharger := positivity) [abs_of_nonneg, NNReal.smul_def] using
      H (NNReal.mk ε hε.le) this
  · simp (discharger := positivity) only [Function.comp_apply, Real.norm_of_nonneg] at H
    exact H (by positivity)

end PolynormableSpace

namespace WithSeminorms

variable {p : SeminormFamily 𝕜 E ι} {q : SeminormFamily 𝕜 F κ}

theorem isBigOTVS_iff_le_continuous (hp : WithSeminorms p) [PolynormableSpace 𝕜 F] :
    f =O[𝕜; l] g ↔ ∀ i : ι, ∃ q : Seminorm 𝕜 F, Continuous q ∧ p i ∘ f ≤ᶠ[l] (q ∘ g) := by
  sorry

theorem isBigOTVS_iff_le (hp : WithSeminorms p) (hq : WithSeminorms q) :
    f =O[𝕜; l] g ↔ ∀ i : ι, ∃ s : Finset κ, ∃ C : ℝ≥0, p i ∘ f ≤ᶠ[l] ((C • s.sup q) ∘ g) := by
  have := hq.toPolynormableSpace
  rw [hp.isBigOTVS_iff_le_continuous]
  congrm ∀ i, ?_
  constructor
  · intro ⟨r, r_cont, hr⟩
    obtain ⟨s, C, C_ne, hC⟩ := Seminorm.bound_of_continuous hq r r_cont
    exact ⟨s, C, hr.mono fun x hx ↦ hx.trans (hC _)⟩
  · intro ⟨s, C, hC⟩
    use C • s.sup q
    have := hq.topologicalAddGroup
    use (Seminorm.continuous_finsetSup fun i _ ↦ hq.continuous_seminorm i).const_smul _

theorem isBigOTVS_iff (hp : WithSeminorms p) (hq : WithSeminorms q) :
    f =O[𝕜; l] g ↔ ∀ i : ι, ∃ s : Finset κ, (p i ∘ f) =O[l] (↑(s.sup q) ∘ g) := by
  simp_rw [hp.isBigOTVS_iff_le hq, Filter.EventuallyLE]
  congrm ∀ i, ∃ s, ?_
  constructor
  · intro ⟨C, hC⟩
    exact .of_bound C <| by simpa (discharger := positivity) [abs_of_nonneg]
  · rw [Asymptotics.isBigO_iff']
    intro ⟨C, C_pos, hC⟩
    refine ⟨C.toNNReal, ?_⟩
    convert hC using 2
    simp (discharger := positivity) [abs_of_nonneg, NNReal.smul_def]

theorem isLittleOTVS_iff_le_continuous (hp : WithSeminorms p) [PolynormableSpace 𝕜 F] :
    f =o[𝕜; l] g ↔
      ∀ i : ι, ∃ q : Seminorm 𝕜 F, Continuous q ∧
        ∀ ε : ℝ≥0, ε ≠ 0 → p i ∘ f ≤ᶠ[l] ((ε • q) ∘ g) := by sorry

theorem isLittleOTVS_iff_le (hp : WithSeminorms p) (hq : WithSeminorms q) :
    f =o[𝕜; l] g ↔
      ∀ i : ι, ∃ s : Finset κ, ∀ ε : ℝ≥0, ε ≠ 0 → p i ∘ f ≤ᶠ[l] ((ε • s.sup q) ∘ g) := by
  have := hq.toPolynormableSpace
  rw [hp.isLittleOTVS_iff_le_continuous]
  congrm ∀ i, ?_
  constructor
  · intro ⟨r, r_cont, hr⟩
    obtain ⟨s, C, C_ne, hC⟩ := Seminorm.bound_of_continuous hq r r_cont
    refine ⟨s, fun ε ε_ne ↦ (hr (ε/C) (by positivity)).mono fun x hx ↦ ?_⟩
    simp only [Function.comp_apply, Seminorm.le_def, smul_apply] at hx hC ⊢
    grw [hx, hC _, ← mul_smul, div_mul_cancel₀ _ C_ne]
  · intro ⟨s, hs⟩
    have := hq.topologicalAddGroup
    use s.sup q, Seminorm.continuous_finsetSup fun i _ ↦ hq.continuous_seminorm i

theorem isLittleOTVS_iff (hp : WithSeminorms p) (hq : WithSeminorms q) :
    f =o[𝕜; l] g ↔ ∀ i : ι, ∃ s : Finset κ, (p i ∘ f) =o[l] ((s.sup q : Seminorm 𝕜 F) ∘ g) := by
  simp_rw [hp.isLittleOTVS_iff_le hq, Filter.EventuallyLE, Asymptotics.isLittleO_iff]
  congrm ∀ i, ∃ s, ?_
  constructor <;> intro H ε hε
  · have : NNReal.mk ε hε.le ≠ 0 := by simpa [← NNReal.coe_ne_zero] using hε.ne'
    simpa [abs_of_nonneg, NNReal.smul_def] using H _ this
  · simp (discharger := positivity) only [Function.comp_apply, Real.norm_of_nonneg] at H
    exact H (by positivity)

end WithSeminorms

end
