module

public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic.TypeStar
public import Mathlib.RingTheory.Derivation.Basic

@[expose] public section

noncomputable section

open Polynomial

namespace GroundTheory.Global

section MatrixJacobi

variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]

def matrixGeomSeries (M : Matrix n n R) : Matrix n n (PowerSeries R) :=
  Matrix.of fun i j => PowerSeries.mk fun k => (M ^ k) i j

theorem coeff_map_C_mul_matrixGeomSeries (M : Matrix n n R) (k : ℕ) (i j : n) :
    PowerSeries.coeff k ((M.map PowerSeries.C * matrixGeomSeries M) i j) = (M ^ (k + 1)) i j := by

  rw [pow_succ', Matrix.mul_apply, Matrix.mul_apply, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp [matrixGeomSeries, PowerSeries.coeff_C_mul]

theorem one_sub_X_smul_mul_matrixGeomSeries (M : Matrix n n R) :
    (1 - (PowerSeries.X : PowerSeries R) • M.map PowerSeries.C) * matrixGeomSeries M = 1 := by
  ext i j k
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.sub_apply, Matrix.smul_apply,
    smul_eq_mul, map_sub]
  rcases k with _ | k
  · simp [matrixGeomSeries, Matrix.one_apply]
  · rw [PowerSeries.coeff_succ_X_mul, coeff_map_C_mul_matrixGeomSeries]
    by_cases h : i = j <;> simp [matrixGeomSeries, Matrix.one_apply, h]

theorem trace_matrixGeomSeries_mul (M : Matrix n n R) :
    (matrixGeomSeries M * M.map PowerSeries.C).trace =
      PowerSeries.mk fun k => (M ^ (k + 1)).trace := by
  ext k

  rw [PowerSeries.coeff_mk, pow_succ, Matrix.trace, Matrix.trace, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_

  rw [Matrix.diag_apply, Matrix.diag_apply, Matrix.mul_apply, Matrix.mul_apply, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp [matrixGeomSeries, PowerSeries.coeff_mul_C]

theorem coe_charpolyRev (M : Matrix n n R) :
    ((M.charpolyRev : R[X]) : PowerSeries R) =
      (1 - (PowerSeries.X : PowerSeries R) • M.map PowerSeries.C).det := by
  rw [Matrix.charpolyRev, ← Polynomial.coeToPowerSeries.ringHom_apply, RingHom.map_det]
  congr 1
  ext i j : 1
  by_cases h : i = j <;>
    simp [h, Polynomial.coeToPowerSeries.ringHom_apply] <;> ring

theorem coe_derivative_charpolyRev (M : Matrix n n R) :
    ((derivative M.charpolyRev : R[X]) : PowerSeries R) =
      -(M.charpolyRev : PowerSeries R) * PowerSeries.mk fun k => (M ^ (k + 1)).trace := by
  set T : PowerSeries R := PowerSeries.X
  set N : Matrix n n (PowerSeries R) := M.map PowerSeries.C
  set A : Matrix n n (PowerSeries R) := 1 - T • N
  set B := matrixGeomSeries M
  have hAB : A * B = 1 := one_sub_X_smul_mul_matrixGeomSeries M

  set ψ : R[X] →+* (PowerSeries R)[X] :=
    (Polynomial.compRingHom (Polynomial.C T + Polynomial.X)).comp
      (Polynomial.mapRingHom PowerSeries.C)
  have hψ : ∀ p : R[X], ψ p = (p.map PowerSeries.C).comp (Polynomial.C T + Polynomial.X) :=
    fun p => rfl
  have hfac : ψ M.charpolyRev =
      Polynomial.C A.det * (1 + (Polynomial.X : (PowerSeries R)[X]) •
        (-(B * N)).map Polynomial.C).det := by
    rw [Matrix.charpolyRev, RingHom.map_det, RingHom.map_det, ← Matrix.det_mul]
    congr 1
    have h1 : A.map Polynomial.C * (1 + (Polynomial.X : (PowerSeries R)[X]) •
        (-(B * N)).map Polynomial.C) =
        A.map Polynomial.C - (Polynomial.X : (PowerSeries R)[X]) • N.map Polynomial.C := by
      rw [mul_add, mul_one, Matrix.mul_smul, ← Matrix.map_mul, Matrix.mul_neg,
        ← Matrix.mul_assoc, hAB, Matrix.one_mul, Matrix.map_neg _ (map_neg Polynomial.C), smul_neg, sub_eq_add_neg]
    rw [show (Polynomial.C : PowerSeries R →+* (PowerSeries R)[X]).mapMatrix A =
      A.map Polynomial.C from rfl, h1]
    ext i j
    by_cases h : i = j <;>
      simp [hψ, A, N, T, h] <;> ring
  have hder : (derivative (ψ M.charpolyRev)).eval 0 =
      ((derivative M.charpolyRev : R[X]) : PowerSeries R) := by
    rw [hψ, Polynomial.derivative_comp, Polynomial.derivative_add, Polynomial.derivative_C,
      Polynomial.derivative_X, zero_add, one_mul, Polynomial.eval_comp, Polynomial.derivative_map,
      Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X, add_zero, Polynomial.eval_map,
      Polynomial.eval₂_C_X_eq_coe]
  rw [← hder, hfac, Polynomial.derivative_C_mul, Polynomial.eval_mul, Polynomial.eval_C,
    Matrix.derivative_det_one_add_X_smul, Matrix.trace_neg, ← coe_charpolyRev,
    ← trace_matrixGeomSeries_mul, mul_neg, neg_mul]

/-- Newton's recurrence for the coefficients of the reverse characteristic polynomial. -/
theorem charpolyRev_coeff_succ_mul (M : Matrix n n R) (m : ℕ) :
    M.charpolyRev.coeff (m + 1) * (m + 1 : R) =
      -∑ p ∈ Finset.antidiagonal m, M.charpolyRev.coeff p.1 * (M ^ (p.2 + 1)).trace := by
  simpa only [Polynomial.coeff_coe, Polynomial.coeff_derivative, map_neg,
    PowerSeries.coeff_mul, PowerSeries.coeff_mk, neg_mul] using
    congrArg (PowerSeries.coeff (R := R) m) (coe_derivative_charpolyRev M)

end MatrixJacobi

section Traces

open Finset

variable {R ι ι' : Type*} [CommRing R] [HasUniqueDiv R] [Fintype ι] [DecidableEq ι]
  [Fintype ι'] [DecidableEq ι']

/-- Agreement of the first `d` power traces determines the degree-`d` coefficient of the
reverse characteristic polynomial, even for matrices of different sizes. -/
theorem coeff_charpolyRev_eq_of_trace_powers (A : Matrix ι ι R) (B : Matrix ι' ι' R) (d : ℕ)
    (h : ∀ j, 0 < j → j ≤ d → (A ^ j).trace = (B ^ j).trace) :
    A.charpolyRev.coeff d = B.charpolyRev.coeff d := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    cases d with
    | zero => simp [Polynomial.coeff_zero_eq_eval_zero, Matrix.eval_charpolyRev]
    | succ m =>
      apply nsmul_right_injective (M := R) (Nat.succ_ne_zero m)
      simp only [nsmul_eq_mul', Nat.cast_succ]
      rw [charpolyRev_coeff_succ_mul, charpolyRev_coeff_succ_mul]
      congr 1
      refine Finset.sum_congr rfl fun p hp => ?_
      have := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
      rw [ih p.1 (by lia) (fun j hj hle => h j hj (by lia)), h _ (by lia) (by lia)]

/-- Matrices of size `n` have equal characteristic polynomials if their first `n` positive
power traces agree. -/
theorem charpoly_eq_of_trace_powers (A B : Matrix ι ι R)
    (h : ∀ m, 0 < m → m ≤ Fintype.card ι → (A ^ m).trace = (B ^ m).trace) :
    A.charpoly = B.charpoly := by
  nontriviality R
  apply (Polynomial.ext_iff_natDegree_le A.charpoly_natDegree_eq_dim.le B.charpoly_natDegree_eq_dim.le).mpr
  intro i hi
  have he := coeff_charpolyRev_eq_of_trace_powers A B (Fintype.card ι - i)
    (fun j hj hj' => h j hj (by lia))
  simpa only [← Matrix.reverse_charpoly, Polynomial.coeff_reverse, Matrix.charpoly_natDegree_eq_dim,
    Polynomial.revAt_le (Nat.sub_le ..), Nat.sub_sub_self hi] using he

end Traces

section LogSeries

variable {k : Type*} [Field k] [CharZero k]

end LogSeries

section Endomorphism

variable {k W W' : Type*} [Field k] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
  [AddCommGroup W'] [Module k W'] [FiniteDimensional k W']

theorem reverse_charpoly_eq_charpolyRev {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι k W) (A : Module.End k W) :
    A.charpoly.reverse = (LinearMap.toMatrix b b A).charpolyRev := by
  rw [← Matrix.reverse_charpoly, LinearMap.charpoly_toMatrix]

theorem constantCoeff_reverse_charpoly (A : Module.End k W) :
    PowerSeries.constantCoeff (A.charpoly.reverse : PowerSeries k) = 1 := by
  rw [Polynomial.constantCoeff_coe, Polynomial.coeff_zero_reverse,
    (LinearMap.charpoly_monic A).leadingCoeff]

theorem coe_derivative_reverse_charpoly (A : Module.End k W) :
    ((derivative A.charpoly.reverse : k[X]) : PowerSeries k) =
      -(A.charpoly.reverse : PowerSeries k) *
        PowerSeries.mk fun m => LinearMap.trace k W (A ^ (m + 1)) := by
  classical
  let b := Module.Free.chooseBasis k W
  rw [reverse_charpoly_eq_charpolyRev b, coe_derivative_charpolyRev]
  congr 2
  funext m
  rw [LinearMap.trace_eq_matrix_trace k b, LinearMap.toMatrix_pow]

theorem reverse_charpoly_eq_of_trace_pow_eq [CharZero k] (A : Module.End k W)
    (B : Module.End k W')
    (h : ∀ m, 0 < m → LinearMap.trace k W (A ^ m) = LinearMap.trace k W' (B ^ m)) :
    A.charpoly.reverse = B.charpoly.reverse := by
  classical
  let b := Module.finBasis k W
  let b' := Module.finBasis k W'
  rw [reverse_charpoly_eq_charpolyRev b, reverse_charpoly_eq_charpolyRev b']
  ext d
  apply coeff_charpolyRev_eq_of_trace_powers
  intro n hn _
  simpa only [LinearMap.trace_eq_matrix_trace k b, LinearMap.trace_eq_matrix_trace k b',
    LinearMap.toMatrix_pow] using h n hn

end Endomorphism

end GroundTheory.Global
