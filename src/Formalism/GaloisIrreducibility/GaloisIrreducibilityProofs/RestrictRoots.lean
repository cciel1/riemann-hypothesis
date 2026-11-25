module

import Development.AbelianVarietyTheory.Proofs.CharacterTheory.CharpolyBlockAndInvariantUnderStabilizerNilradic
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.RootsCharpolyPowEqMapPow
public import Formalism.GaloisIrreducibility.Statement
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Lemma
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Eigenspace.Basic

@[expose] public section

namespace Formalism.GaloisIrreducibility

open Module Polynomial

section SlopeTestRemainingChoices
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

lemma rr_charpoly_compl (φ : Module.End K V) (P Q : Submodule K V) (hPQ : IsCompl P Q)
    (hP : ∀ x ∈ P, φ x ∈ P) (hQ : ∀ x ∈ Q, φ x ∈ Q) :
    φ.charpoly = (φ.restrict hP).charpoly * (φ.restrict hQ).charpoly := by
  have hconj : (Submodule.prodEquivOfIsCompl P Q hPQ).symm.conj φ = (φ.restrict hP).prodMap (φ.restrict hQ) := by
    apply LinearMap.ext
    rintro ⟨p, q⟩
    simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_symm, Submodule.coe_prodEquivOfIsCompl', LinearMap.prodMap_apply]
    rw [map_add φ, ← LinearMap.coe_restrict_apply hP p, ← LinearMap.coe_restrict_apply hQ q,
      map_add, Submodule.prodEquivOfIsCompl_symm_apply_left,
      Submodule.prodEquivOfIsCompl_symm_apply_right]
    simp
  rw [← LinearEquiv.charpoly_conj (Submodule.prodEquivOfIsCompl P Q hPQ).symm φ, hconj, LinearMap.charpoly_prodMap]

end SlopeTestRemainingChoices

/-- The roots of the characteristic polynomial of a power are the powers of the roots,
with multiplicities. -/
lemma rr_roots_pow {K V : Type} [Field K] [IsAlgClosed K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (A : Module.End K V) (q : ℕ) :
    (A ^ q).charpoly.roots = A.charpoly.roots.map (· ^ q) := by
  let b := Module.finBasis K V
  rw [← LinearMap.charpoly_toMatrix (A ^ q) b, ← LinearMap.charpoly_toMatrix A b,
    ← LinearMap.toMatrix_pow]
  exact GlobalTheory.CharpolyPow.roots_charpoly_pow K _ q _

theorem restrict_roots_to_subfield : RestrictRoots := by
  unfold RestrictRoots
  intro K V _ _ _ _ _ τ F q hF W hτ hFW
  let FW := F.toLinearMap.restrict hFW
  have hinj : Function.Injective FW := fun x y h => Subtype.ext (F.injective (congrArg Subtype.val h))
  let eW := LinearEquiv.ofInjectiveEndo FW hinj
  have hconj : eW.conj (τ.restrict hτ) = (τ.restrict hτ) ^ q := by
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := eW.surjective x
    rw [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      Module.End.pow_restrict q hτ]
    exact Subtype.ext (hF y)
  constructor
  · exact Polynomial.roots.le_of_dvd (LinearMap.charpoly_monic τ).ne_zero
      ⟨_, GlobalTheory.CuspGL.charpoly_eq_restrict_mul_mapQ W τ hτ⟩
  · have h1 := rr_roots_pow (τ.restrict hτ) q
    rw [← hconj, LinearEquiv.charpoly_conj] at h1
    exact h1.symm

end Formalism.GaloisIrreducibility
