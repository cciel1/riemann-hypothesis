module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

universe u_1 u_2

namespace Bl.general_b_fact_second_bis_form

open Metric Set

theorem goal1 {E : Type u_1} {F : Type u_2} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] {f : E → F} {y : E} {δ M : ℝ}
    (hδ : 0 < δ) (hf : DifferentiableOn ℂ f (Metric.ball y δ))
    (hM : ∀ z ∈ Metric.ball y δ, ‖f z‖ ≤ M) :
    ‖fderiv ℂ f y‖ ≤ M / δ := by
  -- The odd difference vanishes at zero and has twice the derivative of `f` at `y`.
  let g (z : E) := f (y + z) - f (y - z)
  have hplus : MapsTo (y + ·) (ball 0 δ) (ball y δ) := by
    intro z hz
    simpa [mem_ball, dist_eq_norm] using hz
  have hminus : MapsTo (y - ·) (ball 0 δ) (ball y δ) := by
    intro z hz
    simpa [mem_ball, dist_eq_norm] using hz
  have hg : DifferentiableOn ℂ g (ball 0 δ) :=
    (hf.comp ((differentiableOn_const y).add differentiableOn_id) hplus).sub
      (hf.comp ((differentiableOn_const y).sub differentiableOn_id) hminus)
  have hG := Complex.norm_fderiv_le_div_of_mapsTo_ball hg (R₂ := 2 * M) (by
    intro z hz
    simpa [g, mem_closedBall, two_mul] using (norm_sub_le _ _).trans
      (add_le_add (hM _ (hplus hz)) (hM _ (hminus hz)))) hδ
  have hD := (hf.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hδ))).hasFDerivAt
  have hp : HasFDerivAt (fun z => f (y + z)) (fderiv ℂ f y) 0 := by
    exact (hasFDerivAt_comp_add_left y).mpr (by simpa using hD)
  have hm : HasFDerivAt (fun z => f (y - z)) (-(fderiv ℂ f y)) 0 := by
    simpa [Function.comp_def] using (show HasFDerivAt f (fderiv ℂ f y) (y - 0) by simpa using hD).comp 0
      ((hasFDerivAt_id (𝕜 := ℂ) (0 : E)).const_sub y)
  have hd : HasFDerivAt g (fderiv ℂ f y - -fderiv ℂ f y) 0 := hp.sub hm
  change ‖fderiv ℂ g 0‖ ≤ _ at hG
  rw [hd.fderiv, sub_neg_eq_add, ← two_smul ℂ, norm_smul, Complex.norm_two] at hG
  linarith [show 2 * M / δ = 2 * (M / δ) by ring]

end Bl.general_b_fact_second_bis_form
