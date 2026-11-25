module

import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RepresentationTheory.Basic

@[expose] public section

open Module

namespace Bl.RankOneOrbitForms

variable {K : Type} [Field K] {G : Type} [Group G] {T : Type} [AddCommGroup T] [Module K T]

private lemma rank_one_form [FiniteDimensional K T] (f : T →ₗ[K] T) (h1 : finrank K (LinearMap.range f) = 1) :
    ∃ (φ : T →ₗ[K] K) (v : T), v ≠ 0 ∧ φ ≠ 0 ∧ f = φ.smulRight v := by
  let e : LinearMap.range f ≃ₗ[K] K := LinearEquiv.ofFinrankEq _ _ (by simpa using h1)
  let φ := e.toLinearMap.comp f.rangeRestrict
  let v := e.symm (1 : K)
  have hv : v ≠ 0 := by
    simpa only [v, map_zero] using e.symm.injective.ne (one_ne_zero : (1 : K) ≠ 0)
  have hφ : Function.Surjective φ := e.surjective.comp f.surjective_rangeRestrict
  refine ⟨φ, v, fun h => hv (Subtype.ext h), LinearMap.ne_zero_of_surjective hφ, ?_⟩
  ext x
  change f x = ((e (f.rangeRestrict x) • e.symm 1 : LinearMap.range f) : T)
  rw [← e.symm.map_smul, smul_eq_mul, mul_one, e.symm_apply_apply]
  rfl

private lemma span_orbit (τ : Representation K G T)
    (hirr : ∀ W : Submodule K T, (∀ g : G, ∀ w ∈ W, τ g w ∈ W) → W = ⊥ ∨ W = ⊤)
    (v : T) (hv : v ≠ 0) : Submodule.span K (Set.range fun g => τ g v) = ⊤ := by
  have hinvar : ∀ g : G, ∀ w ∈ Submodule.span K (Set.range fun g => τ g v),
      τ g w ∈ Submodule.span K (Set.range fun g => τ g v) := by
    intro g
    change Submodule.span K (Set.range fun h => τ h v) ≤
      (Submodule.span K (Set.range fun h => τ h v)).comap (τ g)
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨h, rfl⟩
    exact Submodule.subset_span ⟨g * h, by simp [map_mul]⟩
  have hvspan : v ∈ Submodule.span K (Set.range fun g => τ g v) :=
    Submodule.subset_span ⟨1, by simp⟩
  exact (hirr _ hinvar).resolve_left fun h => hv (by simpa [h] using hvspan)

private lemma select {ι M : Type} [AddCommGroup M] [Module K M] [FiniteDimensional K M]
    (f : ι → M) (r : ℕ) (hr : finrank K (Submodule.span K (Set.range f)) = r) :
    ∃ s : Fin r → ι, LinearIndependent K (f ∘ s) ∧
      Submodule.span K (Set.range (f ∘ s)) = Submodule.span K (Set.range f) := by
  obtain ⟨κ, a, -, hsp, hli⟩ := exists_linearIndependent' K f
  have : Finite κ := hli.finite
  let _ : Fintype κ := Fintype.ofFinite κ
  have hc : Fintype.card κ = r := by
    rw [← finrank_span_eq_card hli, hsp, hr]
  let e : Fin r ≃ κ := (Fintype.equivFinOfCardEq hc).symm
  refine ⟨a ∘ e, hli.comp e e.injective, ?_⟩
  rw [← Function.comp_assoc, e.surjective.range_comp]
  exact hsp

theorem goal1 [FiniteDimensional K T] (τ : Representation K G T)
    (hirr : ∀ W : Submodule K T, (∀ g : G, ∀ w ∈ W, τ g w ∈ W) → W = ⊥ ∨ W = ⊤)
    (ε₀ ε : T →ₗ[K] T) (h1 : finrank K (LinearMap.range ε₀) = 1) :
    ∃ (γ δ : Fin (finrank K (LinearMap.range ε)) → G)
      (c : Matrix (Fin (finrank K (LinearMap.range ε))) (Fin (finrank K (LinearMap.range ε))) K),
      c.det ≠ 0 ∧
      (∀ i j, c i j = LinearMap.trace K T (ε₀ ∘ₗ τ (δ i) ∘ₗ ε ∘ₗ τ (γ j))) ∧
      (∀ i j, ε₀ ∘ₗ τ (δ i) ∘ₗ ε ∘ₗ τ (γ j) ∘ₗ ε₀ = c i j • ε₀) ∧
      ∑ j, ∑ i, c⁻¹ j i • (ε ∘ₗ τ (γ j) ∘ₗ ε₀ ∘ₗ τ (δ i) ∘ₗ ε) = ε := by
  obtain ⟨φ, v, hv, hφ, rfl⟩ := rank_one_form ε₀ h1
  have hspanT := span_orbit τ hirr v hv
  have hspanR : Submodule.span K (Set.range fun g => ε (τ g v)) = LinearMap.range ε := by
    rw [Set.range_comp', ← Submodule.map_span, hspanT, Submodule.map_top]
  obtain ⟨γ, hγ, hγspan⟩ := select (fun g => ε (τ g v)) (finrank K (LinearMap.range ε))
    (by rw [hspanR])
  have hueq := hγspan.trans hspanR
  let w : G → Fin (finrank K (LinearMap.range ε)) → K := fun g j => φ (τ g (ε (τ (γ j) v)))
  have hw : Submodule.span K (Set.range w) = ⊤ := by
    let evalOrbit : T →ₗ[K] G → K := LinearMap.pi fun g => φ ∘ₗ τ g
    have hker : LinearMap.ker evalOrbit = ⊥ := by
      apply LinearMap.ker_eq_bot'.mpr
      intro x hx
      by_contra hx0
      exact hφ (LinearMap.ext_on_range (span_orbit τ hirr x hx0)
        (fun g => congrFun hx g))
    exact span_flip_eq_top_iff_linearIndependent.mpr (hγ.map' evalOrbit hker)
  obtain ⟨δ, hδ, -⟩ := select w (finrank K (LinearMap.range ε))
    (by rw [hw, finrank_top, Module.finrank_fin_fun])
  let c : Matrix (Fin (finrank K (LinearMap.range ε))) (Fin (finrank K (LinearMap.range ε))) K :=
    Matrix.of fun i j => φ (τ (δ i) (ε (τ (γ j) v)))
  have hc : IsUnit c := Matrix.linearIndependent_row_iff_isUnit.mp hδ
  have hcd : IsUnit c.det := (Matrix.isUnit_iff_isUnit_det c).mp hc
  refine ⟨γ, δ, c, hcd.ne_zero, ?_, ?_, ?_⟩
  · intro i j
    rw [show (φ.smulRight v) ∘ₗ τ (δ i) ∘ₗ ε ∘ₗ τ (γ j)
        = (φ ∘ₗ τ (δ i) ∘ₗ ε ∘ₗ τ (γ j)).smulRight v from LinearMap.ext fun _ => rfl,
      LinearMap.trace_smulRight]
    rfl
  · intro i j
    ext x
    simp [c, smul_smul, mul_comm]
  · ext x
    have hx : ε x ∈ Submodule.span K (Set.range ((fun g => ε (τ g v)) ∘ γ)) :=
      by rw [hueq]; exact LinearMap.mem_range_self ε x
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hx
    simp only [Function.comp_apply] at ha
    have hcoef : ∀ i, φ (τ (δ i) (ε x)) = ∑ k, c i k * a k := by
      intro i
      rw [← ha]

      simp [c, map_sum, map_smul, mul_comm]
    have hinv : ∀ j, ∑ i, c⁻¹ j i * ∑ k, c i k * a k = a j := by
      intro j
      have := congrFun (show Matrix.mulVec c⁻¹ (Matrix.mulVec c a) = a by
        rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul c hcd, Matrix.one_mulVec]) j
      simpa [Matrix.mulVec, dotProduct] using this
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
      LinearMap.smulRight_apply, map_smul, hcoef]
    rw [← ha]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hinv j, Finset.sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul]

end Bl.RankOneOrbitForms
