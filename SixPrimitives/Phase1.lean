import SixPrimitives.Phase0
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-! # Ismail's Primitives — Phase 1: Standard Lemmas -/

open MeasureTheory ProbabilityTheory Filter Real BigOperators Topology Set
open scoped ENNReal NNReal

namespace SixPrimitives.Phase1

-- §0  LOCAL INFRASTRUCTURE

section LocalInfrastructure

noncomputable def klDiv {α : Type*} [Fintype α] (P Q : PMF α) : ℝ :=
  ∑ x : α, (P x).toReal * Real.log ((P x).toReal / (Q x).toReal)

noncomputable def tvDist {α : Type*} [Fintype α] (P Q : PMF α) : ℝ :=
  (1 / 2) * ∑ x : α, |(P x).toReal - (Q x).toReal|

/-- Equal-weight mixture of two PMFs: M = ½(P + Q). -/
noncomputable def mixPMF {α : Type*} (P Q : PMF α) : PMF α :=
  ⟨fun x => (P x + Q x) / 2, by
    apply ENNReal.summable.hasSum_iff.mpr
    simp_rw [ENNReal.add_div, div_eq_mul_inv]
    rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, ENNReal.tsum_mul_right,
        P.tsum_coe, Q.tsum_coe]
    simp only [one_mul]
    rw [← two_mul, ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]⟩

/-- Concrete instantiation of conditional entropy H(A | X). -/
noncomputable def condEntropyOf {Ω A X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace X]
    [Fintype A] [MeasurableSingletonClass A]
    (μ : Measure Ω) (A_rv : Ω → A) (X_rv : Ω → X) : ℝ :=
  ∫ ω, ∑ a : A,
    -(μ[(A_rv ⁻¹' {a}).indicator (fun _ => (1 : ℝ)) | MeasurableSpace.comap X_rv inferInstance] ω *
      Real.log (μ[(A_rv ⁻¹' {a}).indicator (fun _ => (1 : ℝ)) | MeasurableSpace.comap X_rv inferInstance] ω)) ∂μ

lemma tvDist_nonneg {α : Type*} [Fintype α] (P Q : PMF α) : 0 ≤ tvDist P Q :=
  mul_nonneg (by norm_num) (Finset.sum_nonneg (fun x _ => abs_nonneg _))

private lemma PMF_sum_toReal {α : Type*} [Fintype α] (p : PMF α) :
    ∑ x : α, (p x).toReal = 1 := by
  have hraw : ∑ x : α, p.1 x = 1 := by
    have := p.2.tsum_eq; rwa [tsum_fintype] at this
  have hfin : ∀ x : α, p.1 x ≠ ⊤ := fun x => by
    have h1 : p.1 x ≤ 1 := by
      calc p.1 x ≤ ∑ y : α, p.1 y :=
            Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ x)
        _ = 1 := hraw
    exact (h1.trans_lt (by norm_num : (1 : ℝ≥0∞) < ⊤)).ne
  have key : (∑ x : α, p.1 x).toReal = ∑ x : α, (p.1 x).toReal :=
    ENNReal.toReal_sum (s := Finset.univ) (fun x _ => hfin x)
  rw [hraw, ENNReal.toReal_one] at key
  exact key.symm

/-- Convert a finite probability measure on a Fintype into a PMF,
    using the singleton-measure decomposition. -/
noncomputable def measureToPMF {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure α) [IsProbabilityMeasure μ] : PMF α :=
  ⟨fun a => μ {a},
   -- HasSum proof: ∑ a, μ{a} = μ univ = 1
   have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset α) : Set α) (fun a => ({a} : Set α)) :=
     fun x _ y _ h => Set.disjoint_singleton.mpr h
   have hmeas : ∀ a ∈ (Finset.univ : Finset α), MeasurableSet ({a} : Set α) :=
     fun a _ => measurableSet_singleton a
   have huniv : ⋃ a ∈ (Finset.univ : Finset α), ({a} : Set α) = Set.univ := by ext; simp
   have hsum : ∑ a ∈ Finset.univ, μ {a} = 1 := by
     rw [← measure_biUnion_finset hdisj hmeas, huniv, measure_univ]
   have hsum' : ∑ a : α, μ {a} = 1 := by simp [hsum]
   by simpa [hsum'] using (hasSum_fintype (fun a : α => μ {a}))⟩

lemma measureToPMF_apply {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ : Measure α) [IsProbabilityMeasure μ] (a : α) :
    (measureToPMF μ) a = μ {a} := rfl

lemma tvDist_le_one {α : Type*} [Fintype α] (P Q : PMF α) : tvDist P Q ≤ 1 := by
  simp only [tvDist]
  suffices h : ∑ x : α, |(P x).toReal - (Q x).toReal| ≤ 2 by linarith
  have hP := PMF_sum_toReal P
  have hQ := PMF_sum_toReal Q
  calc ∑ x : α, |(P x).toReal - (Q x).toReal|
      ≤ ∑ x : α, ((P x).toReal + (Q x).toReal) :=
          Finset.sum_le_sum fun x _ => by
            have hPnn : 0 ≤ (P x).toReal := ENNReal.toReal_nonneg
            have hQnn : 0 ≤ (Q x).toReal := ENNReal.toReal_nonneg
            rw [abs_le]; constructor <;> linarith
    _ = ∑ x : α, (P x).toReal + ∑ x : α, (Q x).toReal := Finset.sum_add_distrib
    _ = 2 := by rw [hP, hQ]; norm_num

end LocalInfrastructure

-- §1  REAL ANALYSIS AUXILIARY LEMMAS

section RealAnalysisAux

lemma log_le_sub_one {x : ℝ} (hx : 0 < x) : Real.log x ≤ x - 1 := by
  linarith [Real.add_one_le_exp (Real.log x), Real.exp_log hx]

lemma log_one_add_le {t : ℝ} (ht : -1 < t) : Real.log (1 + t) ≤ t :=
  by linarith [log_le_sub_one (by linarith : (0 : ℝ) < 1 + t)]

lemma neg_log_second_order {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    (1 - x) + (1 - x) ^ 2 / 2 ≤ -Real.log x := by
  suffices h : Real.log x + (1 - x) + (1 - x) ^ 2 / 2 ≤ 0 by linarith
  have hf_cont : ContinuousOn (fun t => Real.log t + (1 - t) + (1 - t) ^ 2 / 2)
      (Set.Icc x 1) := by
    apply ContinuousOn.add (ContinuousOn.add _ _) _
    · exact Real.continuousOn_log.mono (fun t ht => (lt_of_lt_of_le hx ht.1).ne')
    · exact continuousOn_const.sub continuousOn_id
    · exact ((continuousOn_const.sub continuousOn_id).pow 2).div_const 2
  have hderiv : ∀ t ∈ Set.Ioo x 1,
      HasDerivAt (fun t => Real.log t + (1 - t) + (1 - t) ^ 2 / 2) ((1 - t) ^ 2 / t) t := by
    intro t ht
    have ht0 : 0 < t := lt_trans hx ht.1
    have h1 : HasDerivAt Real.log t⁻¹ t := Real.hasDerivAt_log ht0.ne'
    have h2 : HasDerivAt (fun t => (1 : ℝ) - t) (-1) t := by
      simpa using (hasDerivAt_const t 1).sub (hasDerivAt_id t)
    have h3 : HasDerivAt (fun t => (1 - t) ^ 2 / 2) (-(1 - t)) t := by
      convert (h2.pow 2).div_const 2 using 1; ring
    have key : HasDerivAt (fun t => Real.log t + ((1 - t) + (1 - t) ^ 2 / 2))
        (t⁻¹ + (-1 + -(1 - t))) t := h1.add (h2.add h3)
    convert key using 1
    · funext s; ring
    · field_simp [ht0.ne']; ring
  have hf_mono : MonotoneOn (fun t => Real.log t + (1 - t) + (1 - t) ^ 2 / 2)
      (Set.Icc x 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc x 1) hf_cont
    · intro t ht; rw [interior_Icc] at ht
      exact (hderiv t ht).differentiableAt.differentiableWithinAt
    · intro t ht; rw [interior_Icc] at ht
      have ht0 : 0 < t := lt_trans hx ht.1
      rw [(hderiv t ht).deriv]; positivity
  have h1 := hf_mono (left_mem_Icc.mpr hx1) (right_mem_Icc.mpr hx1) hx1
  simp [Real.log_one] at h1; linarith

end RealAnalysisAux

-- §2  BOUNDARY LIMITS FOR BINARY ENTROPY

section BoundaryLimits

lemma tendsto_mul_log_nhdsWithin_zero :
    Tendsto (fun q : ℝ => q * Real.log q) (𝓝[>] 0) (𝓝 0) := by
  have h_bound : ∀ q ∈ Set.Ioc (0 : ℝ) 1, |q * Real.log q| ≤ 2 * Real.sqrt q := by
    intro q ⟨hq0, hq1⟩
    have hlog_neg : Real.log q ≤ 0 := Real.log_nonpos hq0.le hq1
    rw [abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hq0.le hlog_neg)]
    set s := Real.sqrt q
    have hs  : 0 < s     := Real.sqrt_pos.mpr hq0
    have hsq : s ^ 2 = q := Real.sq_sqrt hq0.le
    have hlog_s : Real.log q = 2 * Real.log s := by rw [← hsq, Real.log_pow]; ring
    rw [hlog_s]
    have hkey : -Real.log s ≤ s⁻¹ := by
      have := log_le_sub_one (inv_pos.mpr hs); rw [Real.log_inv] at this; linarith
    calc -(q * (2 * Real.log s))
        = 2 * s ^ 2 * (-Real.log s) := by rw [hsq]; ring
      _ ≤ 2 * s ^ 2 * s⁻¹           := mul_le_mul_of_nonneg_left hkey (by positivity)
      _ = 2 * s                      := by field_simp
  apply squeeze_zero_norm'
  · have hmem : Set.Ioc (0 : ℝ) 1 ∈ 𝓝[Set.Ioi 0] 0 := by
      apply mem_nhdsWithin.mpr
      refine ⟨Set.Ioo (-1) 1, isOpen_Ioo, by norm_num, ?_⟩
      intro x hx
      exact Set.mem_Ioc.mpr ⟨Set.mem_Ioi.mp hx.2, le_of_lt hx.1.2⟩
    exact eventually_of_mem hmem (fun q hq => h_bound q hq)
  · have h_sqrt : Tendsto (fun q : ℝ => Real.sqrt q) (𝓝[>] 0) (𝓝 0) := by
      have hc : Tendsto Real.sqrt (𝓝 0) (𝓝 0) := by
        have htend := Real.continuous_sqrt.continuousAt (x := 0) |>.tendsto
        simp only [Real.sqrt_zero] at htend; exact htend
      exact hc.mono_left nhdsWithin_le_nhds
    simpa using h_sqrt.const_mul 2

lemma tendsto_one_sub_log_nhdsWithin_one :
    Tendsto (fun q : ℝ => (1 - q) * Real.log (1 - q)) (𝓝[<] 1) (𝓝 0) := by
  have h_map : Tendsto (fun q : ℝ => 1 - q) (𝓝[<] 1) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have hcts : ContinuousAt (fun q : ℝ => 1 - q) 1 :=
        (continuous_const.sub continuous_id).continuousAt
      have : Tendsto (fun q : ℝ => 1 - q) (𝓝 1) (𝓝 0) := by simpa using hcts.tendsto
      exact this.mono_left nhdsWithin_le_nhds
    · apply eventually_nhdsWithin_of_forall
      intro q hq; simp only [Set.mem_Iio] at hq; exact sub_pos.mpr hq
  rw [show (fun q : ℝ => (1 - q) * Real.log (1 - q)) =
      (fun x : ℝ => x * Real.log x) ∘ (fun q => 1 - q) from funext (fun q => by simp)]
  exact tendsto_mul_log_nhdsWithin_zero.comp h_map

end BoundaryLimits

-- §3  BINARY ENTROPY AND FANO FUNCTION

section BinaryEntropy

noncomputable def binEntropy (q : ℝ) : ℝ :=
  -(q * Real.log q) - (1 - q) * Real.log (1 - q)

noncomputable def fanoPhi (q : ℝ) (m : ℕ) : ℝ :=
  binEntropy q + q * Real.log ((m : ℝ) - 1)

lemma binEntropy_nonneg {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    0 ≤ binEntropy q := by
  simp only [binEntropy]
  rcases eq_or_lt_of_le hq0 with rfl | hq0'; · simp
  rcases eq_or_lt_of_le hq1 with rfl | hq1'; · simp
  have h1 : Real.log q ≤ 0  := Real.log_nonpos hq0'.le hq1
  have h2 : Real.log (1-q) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
  nlinarith [mul_nonpos_of_nonneg_of_nonpos hq0'.le h1,
             mul_nonpos_of_nonneg_of_nonpos (by linarith : (0:ℝ) ≤ 1-q) h2]

private lemma binEntropy_hasDerivAt {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt binEntropy (Real.log (1 - x) - Real.log x) x := by
  have hxne   : x ≠ 0       := hx0.ne'
  have h1mx   : 0 < 1 - x   := by linarith
  have h1mxne : 1 - x ≠ 0   := h1mx.ne'
  have hd1 : HasDerivAt (fun u => -(u * Real.log u)) (-(Real.log x + 1)) x := by
    have h := (hasDerivAt_id x).mul (Real.hasDerivAt_log hxne)
    simp only [id] at h; convert h.neg using 1; field_simp
  have hd2 : HasDerivAt (fun u => -((1 - u) * Real.log (1 - u)))
      (Real.log (1 - x) + 1) x := by
    have hg : HasDerivAt (fun u => 1 - u) (-1) x := by
      simpa using (hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)
    have hf : HasDerivAt (fun u => u * Real.log u) (Real.log (1 - x) + 1) (1 - x) := by
      have h := (hasDerivAt_id (1 - x)).mul (Real.hasDerivAt_log h1mxne)
      simp only [id] at h; convert h using 1; field_simp
    convert (hf.comp x hg).neg using 1; simp
  convert hd1.add hd2 using 1; simp; ring

private lemma real_continuousAt_log_of_ne {x : ℝ} (hx : x ≠ 0) :
    ContinuousAt Real.log x :=
  Real.continuousOn_log.continuousAt
    (isOpen_compl_singleton.mem_nhds (show x ∈ ({0} : Set ℝ)ᶜ from hx))

lemma binEntropy_continuousOn : ContinuousOn binEntropy (Set.Icc 0 1) := by
  intro q ⟨hq0, hq1⟩
  rcases eq_or_lt_of_le hq0 with rfl | hq0'
  · have hbE0 : binEntropy 0 = 0 := by simp [binEntropy, Real.log_zero]
    rw [ContinuousWithinAt, hbE0]
    suffices h : Tendsto binEntropy (𝓝[Set.Ici 0] 0) (𝓝 0) from
      h.mono_left (nhdsWithin_mono 0 fun x hx => hx.1)
    have hIci : Set.Ici (0 : ℝ) = {0} ∪ Set.Ioi 0 := by
      ext x; simp [le_iff_lt_or_eq, or_comm]
    rw [hIci, nhdsWithin_union, nhdsWithin_singleton, Filter.tendsto_sup]
    refine ⟨?_, ?_⟩
    · simp only [Filter.Tendsto, Filter.map_pure, hbE0]; exact pure_le_nhds 0
    · have h1 : Tendsto (fun q : ℝ => -(q * Real.log q)) (𝓝[>] 0) (𝓝 0) := by
        simpa using tendsto_mul_log_nhdsWithin_zero.neg
      have h2 : Tendsto (fun q : ℝ => (1 - q) * Real.log (1 - q)) (𝓝[>] 0) (𝓝 0) := by
        have hcont : ContinuousAt (fun q : ℝ => (1 - q) * Real.log (1 - q)) 0 :=
          (continuous_const.sub continuous_id).continuousAt.mul
            ((real_continuousAt_log_of_ne (by norm_num : (1 : ℝ) - 0 ≠ 0)).comp
              (continuous_const.sub continuous_id).continuousAt)
        have htend := hcont.tendsto
        simp only [sub_zero, Real.log_one, mul_zero] at htend
        exact htend.mono_left nhdsWithin_le_nhds
      have hsum : Tendsto (fun q : ℝ => -(q * Real.log q) - (1 - q) * Real.log (1 - q))
          (𝓝[>] 0) (𝓝 0) := by simpa using h1.sub h2
      exact hsum.congr' (eventually_nhdsWithin_of_forall fun q _ => rfl)
  · rcases eq_or_lt_of_le hq1 with rfl | hq1'
    · have hbE1 : binEntropy 1 = 0 := by simp [binEntropy, Real.log_one, Real.log_zero]
      rw [ContinuousWithinAt, hbE1]
      suffices h : Tendsto binEntropy (𝓝[Set.Iic 1] 1) (𝓝 0) from
        h.mono_left (nhdsWithin_mono 1 fun x hx => hx.2)
      have hIic : Set.Iic (1 : ℝ) = Set.Iio 1 ∪ {1} := by
        ext x; simp [le_iff_lt_or_eq]
      rw [hIic, nhdsWithin_union, nhdsWithin_singleton, Filter.tendsto_sup]
      refine ⟨?_, ?_⟩
      · have h1 : Tendsto (fun q : ℝ => -(q * Real.log q)) (𝓝[<] 1) (𝓝 0) := by
          have hcont : ContinuousAt (fun q : ℝ => -(q * Real.log q)) 1 :=
            (continuous_id.continuousAt.mul
              (real_continuousAt_log_of_ne (by norm_num : (1 : ℝ) ≠ 0))).neg
          have htend := hcont.tendsto
          simp only [Real.log_one, mul_zero, neg_zero] at htend
          exact htend.mono_left nhdsWithin_le_nhds
        have h2 : Tendsto (fun q : ℝ => (1 - q) * Real.log (1 - q)) (𝓝[<] 1) (𝓝 0) :=
          tendsto_one_sub_log_nhdsWithin_one
        have hsum : Tendsto (fun q : ℝ => -(q * Real.log q) - (1 - q) * Real.log (1 - q))
            (𝓝[<] 1) (𝓝 0) := by simpa using h1.sub h2
        exact hsum.congr' (eventually_nhdsWithin_of_forall fun q _ => rfl)
      · simp only [Filter.Tendsto, Filter.map_pure, hbE1]; exact pure_le_nhds 0
    · exact (binEntropy_hasDerivAt hq0' hq1').continuousAt.continuousWithinAt

lemma binEntropy_concaveOn : ConcaveOn ℝ (Set.Icc 0 1) binEntropy := by
  apply AntitoneOn.concaveOn_of_deriv (convex_Icc 0 1) binEntropy_continuousOn
  · intro x hx
    rw [interior_Icc] at hx
    exact (binEntropy_hasDerivAt hx.1 hx.2).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    intro x hx y hy hxy
    rw [(binEntropy_hasDerivAt hx.1 hx.2).deriv,
        (binEntropy_hasDerivAt hy.1 hy.2).deriv]
    have h1 : Real.log (1 - y) ≤ Real.log (1 - x) :=
      Real.log_le_log (by linarith [hy.2]) (by linarith)
    have h2 : Real.log x ≤ Real.log y := Real.log_le_log hx.1 hxy
    linarith

lemma fanoPhi_concaveOn (m : ℕ) (hm : 2 ≤ m) :
    ConcaveOn ℝ (Set.Icc 0 (1 - 1 / (m : ℝ))) (fun q => fanoPhi q m) := by
  have hm_pos : (0 : ℝ) < m := by exact_mod_cast Nat.lt_of_lt_of_le (by norm_num : 0 < 2) hm
  show ConcaveOn ℝ (Set.Icc 0 (1 - 1 / (m : ℝ)))
      (fun q => binEntropy q + q * Real.log ((m : ℝ) - 1))
  apply ConcaveOn.add
  · exact binEntropy_concaveOn.subset
        (fun q ⟨hq0, hq1⟩ => ⟨hq0, by linarith [div_pos one_pos hm_pos]⟩)
        (convex_Icc _ _)
  · refine ⟨convex_Icc _ _, fun x _ y _ a b _ _ _ => ?_⟩
    simp only [smul_eq_mul]
    have : a * (x * Real.log ((m : ℝ) - 1)) + b * (y * Real.log ((m : ℝ) - 1)) =
           (a * x + b * y) * Real.log ((m : ℝ) - 1) := by ring
    linarith

private lemma fanoPhi_continuousOn (m : ℕ) (hm : 2 ≤ m) :
    ContinuousOn (fun q => fanoPhi q m) (Set.Icc 0 (1 - 1 / (m : ℝ))) := by
  apply ContinuousOn.add
  · exact binEntropy_continuousOn.mono
      (Set.Icc_subset_Icc_right (by
        have : (0 : ℝ) < m := by positivity
        linarith [div_nonneg one_pos.le this.le]))
  · exact continuousOn_id.mul continuousOn_const

lemma fanoPhi_strictMono (m : ℕ) (hm : 2 ≤ m) :
    StrictMonoOn (fun q => fanoPhi q m) (Set.Icc 0 (1 - 1 / (m : ℝ))) := by
  have hm_pos : (0 : ℝ) < m  := by positivity
  have hm_ne  : (m : ℝ) ≠ 0  := hm_pos.ne'
  have hm1_pos : (0 : ℝ) < (m : ℝ) - 1 := by
    have hm2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hm1_ne : (m : ℝ) - 1 ≠ 0 := hm1_pos.ne'
  have hderiv : ∀ q ∈ Set.Ioo (0 : ℝ) (1 - 1 / (m : ℝ)),
      HasDerivAt (fun q => fanoPhi q m)
        (Real.log (1 - q) - Real.log q + Real.log ((m : ℝ) - 1)) q := by
    intro q ⟨hq0, hq1⟩
    have hq1' : q < 1 := by
      have : 0 < 1 / (m : ℝ) := div_pos one_pos hm_pos; linarith
    have hbE  := binEntropy_hasDerivAt hq0 hq1'
    have hlin : HasDerivAt (fun q => q * Real.log ((m : ℝ) - 1))
        (Real.log ((m : ℝ) - 1)) q := by
      simpa using (hasDerivAt_id q).mul_const (Real.log ((m : ℝ) - 1))
    exact hbE.add hlin
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (fanoPhi_continuousOn m hm)
  intro q hq
  rw [interior_Icc] at hq
  have hq0  : 0 < q                := hq.1
  have hq1t : q < 1 - 1 / (m : ℝ) := hq.2
  have hq1  : q < 1 := by
    have : 0 < 1 / (m : ℝ) := div_pos one_pos hm_pos; linarith
  have h1mq : 0 < 1 - q := by linarith
  rw [(hderiv q hq).deriv,
      show Real.log (1 - q) - Real.log q + Real.log ((m : ℝ) - 1) =
           Real.log ((1 - q) * ((m : ℝ) - 1)) - Real.log q from by
        rw [Real.log_mul h1mq.ne' hm1_ne]; ring]
  apply sub_pos.mpr
  apply Real.log_lt_log hq0
  have h  : q * (m : ℝ) < (1 - 1 / (m : ℝ)) * (m : ℝ) :=
    mul_lt_mul_of_pos_right hq1t hm_pos
  have h2 : (1 - 1 / (m : ℝ)) * (m : ℝ) = (m : ℝ) - 1 := by field_simp
  nlinarith

lemma fanoPhi_boundary (m : ℕ) (hm : 2 ≤ m) :
    fanoPhi 0 m = 0 ∧ fanoPhi (1 - 1 / (m : ℝ)) m = Real.log m := by
  refine ⟨by simp [fanoPhi, binEntropy], ?_⟩
  have hm_pos : (0 : ℝ) < m  := by positivity
  have hm_ne  : (m : ℝ) ≠ 0  := hm_pos.ne'
  have hm1_pos : (0 : ℝ) < (m : ℝ) - 1 := by
    have hm2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hm1_ne : (m : ℝ) - 1 ≠ 0 := hm1_pos.ne'
  simp only [fanoPhi, binEntropy]
  rw [show (1 : ℝ) - 1 / (m : ℝ) = ((m : ℝ) - 1) / (m : ℝ) from by field_simp,
      show (1 : ℝ) - ((m : ℝ) - 1) / (m : ℝ) = 1 / (m : ℝ) from by field_simp; ring,
      Real.log_div hm1_ne hm_ne,
      show (1 : ℝ) / (m : ℝ) = ((m : ℝ))⁻¹ from one_div _,
      Real.log_inv]
  field_simp [hm_ne]; ring

lemma exists_fanoRoot_eq (ε : ℝ) (m : ℕ) (hm : 2 ≤ m) (hε : 0 < ε) (hε_lt : ε < Real.log m) :
    ∃ x ∈ Set.Ioo (0:ℝ) (1 - 1 / (m:ℝ)), fanoPhi x m = ε := by
  have hb := fanoPhi_boundary m hm
  have h_cont := fanoPhi_continuousOn m hm
  have h_m_pos : (0:ℝ) ≤ 1 - 1 / (m:ℝ) := by
    have hm2 : (2:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
    rw [sub_nonneg]
    have : 0 < (m:ℝ) := by linarith
    field_simp
    linarith
  have hy : ε ∈ Set.Ioo (fanoPhi 0 m) (fanoPhi (1 - 1 / (m:ℝ)) m) := by
    rw [hb.1, hb.2]
    exact ⟨hε, hε_lt⟩
  exact intermediate_value_Ioo h_m_pos h_cont hy

/-- Root of `fanoPhi · m = ε`; constructed concretely via IVT. -/
noncomputable def fanoRoot (ε : ℝ) (m : ℕ) (hm : 2 ≤ m)
    (hε : 0 < ε) (hε_lt : ε < Real.log m) : ℝ :=
  Classical.choose (exists_fanoRoot_eq ε m hm hε hε_lt)

lemma exists_binEntropy_eq {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2) :
    ∃ x ∈ Set.Ioo (0:ℝ) (1/2), binEntropy x = ε := by
  have h0 : binEntropy 0 = 0 := by simp [binEntropy, Real.log_zero]
  have h_half : binEntropy (1 / 2) = Real.log 2 := by
    simp only [binEntropy]
    have h1 : (1:ℝ) - 1/2 = 1/2 := by norm_num
    rw [h1]
    have h2 : Real.log (1 / 2) = -Real.log 2 := by rw [one_div, Real.log_inv]
    rw [h2]
    ring
  have h_cont : ContinuousOn binEntropy (Set.Icc 0 (1/2)) :=
    binEntropy_continuousOn.mono (by
      intro x hx; rw [Set.mem_Icc] at hx ⊢; constructor; exact hx.1; linarith)
  have h_pos : (0:ℝ) ≤ 1/2 := by norm_num
  have hy : ε ∈ Set.Ioo (binEntropy 0) (binEntropy (1/2)) := by
    rw [h0, h_half]
    exact ⟨hε, hε2⟩
  exact intermediate_value_Ioo h_pos h_cont hy

/-- Inverse of `binEntropy` on `(0, ½)`; constructed concretely via IVT. -/
noncomputable def binEntropyInv (ε : ℝ) : ℝ :=
  if h : 0 < ε ∧ ε < Real.log 2 then
    Classical.choose (exists_binEntropy_eq h.1 h.2)
  else
    0

/-- `binEntropyInv ε` lies in `(0, ½)` and satisfies `binEntropy (binEntropyInv ε) = ε`. -/
theorem binEntropyInv_spec {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2) :
    0 < binEntropyInv ε ∧ binEntropyInv ε < 1 / 2 ∧
    binEntropy (binEntropyInv ε) = ε := by
  have h_and : 0 < ε ∧ ε < Real.log 2 := ⟨hε, hε2⟩
  rw [binEntropyInv, dif_pos h_and]
  have h_exists := Classical.choose_spec (exists_binEntropy_eq hε hε2)
  rcases h_exists with ⟨hx_mem, hx_eq⟩
  rw [Set.mem_Ioo] at hx_mem
  exact ⟨hx_mem.1, hx_mem.2, hx_eq⟩

end BinaryEntropy

-- §4  LE CAM / BRETAGNOLLE–HUBER

section BretagnolleHuber

/-- Le Cam's inequality: P(E) + Q(Eᶜ) ≥ 1 − TV(P, Q). -/
lemma sum_error_ge_one_sub_tv {α : Type*} [Fintype α] [DecidableEq α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (P Q : PMF α) (E : Finset α) :
    (∑ x ∈ E, (P x).toReal) + (∑ x ∈ Finset.univ \ E, (Q x).toReal) ≥ 1 - tvDist P Q := by
  rw [ge_iff_le, ← sub_nonneg]
  simp only [tvDist]
  have hP := PMF_sum_toReal P
  have hQ := PMF_sum_toReal Q
  have hQEc : ∑ x ∈ Finset.univ \ E, (Q x).toReal =
              1 - ∑ x ∈ E, (Q x).toReal := by
    have h : ∑ x ∈ Finset.univ \ E, (Q x).toReal + ∑ x ∈ E, (Q x).toReal =
             ∑ x : α, (Q x).toReal :=
      Finset.sum_sdiff (Finset.subset_univ E)
    linarith
  rw [hQEc]
  have hzero : ∑ x : α, ((P x).toReal - (Q x).toReal) = 0 := by
    rw [Finset.sum_sub_distrib]; linarith
  have hsplit_signed :
      ∑ x ∈ E, ((P x).toReal - (Q x).toReal) +
      ∑ x ∈ Finset.univ \ E, ((P x).toReal - (Q x).toReal) = 0 := by
    have h : ∑ x ∈ Finset.univ \ E, ((P x).toReal - (Q x).toReal) +
             ∑ x ∈ E, ((P x).toReal - (Q x).toReal) =
             ∑ x : α, ((P x).toReal - (Q x).toReal) :=
      Finset.sum_sdiff (Finset.subset_univ E)
    linarith
  have hA : -∑ x ∈ E, |(P x).toReal - (Q x).toReal| ≤
             ∑ x ∈ E, ((P x).toReal - (Q x).toReal) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro x _; exact neg_abs_le _
  have hC : ∑ x ∈ Finset.univ \ E, ((P x).toReal - (Q x).toReal) ≤
             ∑ x ∈ Finset.univ \ E, |(P x).toReal - (Q x).toReal| := by
    apply Finset.sum_le_sum
    intro x _; exact le_abs_self _
  have hsplit_abs :
      ∑ x : α, |(P x).toReal - (Q x).toReal| =
      ∑ x ∈ E, |(P x).toReal - (Q x).toReal| +
      ∑ x ∈ Finset.univ \ E, |(P x).toReal - (Q x).toReal| := by
    have h : ∑ x ∈ Finset.univ \ E, |(P x).toReal - (Q x).toReal| +
             ∑ x ∈ E, |(P x).toReal - (Q x).toReal| =
             ∑ x : α, |(P x).toReal - (Q x).toReal| :=
      Finset.sum_sdiff (Finset.subset_univ E)
    linarith
  have hE_split : ∑ x ∈ E, ((P x).toReal - (Q x).toReal) =
                  ∑ x ∈ E, (P x).toReal - ∑ x ∈ E, (Q x).toReal := by
    rw [Finset.sum_sub_distrib]
  linarith

lemma sum_error_ge_one_sub_tvMeasure {α : Type*} [Fintype α] [DecidableEq α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (E : Finset α) :
    (∑ x ∈ E, (μ {x}).toReal) + (∑ x ∈ Finset.univ \ E, (ν {x}).toReal) ≥
    1 - tvDist (measureToPMF μ) (measureToPMF ν) := by
  have := sum_error_ge_one_sub_tv (measureToPMF μ) (measureToPMF ν) E
  simp only [measureToPMF_apply] at this
  exact this

end BretagnolleHuber

-- §5  DATA-PROCESSING FOR TOTAL VARIATION

section DataProcessingTV

theorem data_processing_tv {α β : Type*} [Fintype α] [Fintype β]
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (P Q : PMF α) (K : α → PMF β) :
    tvDist (P.bind K) (Q.bind K) ≤ tvDist P Q := by
  have hne_top : ∀ (R : PMF α) (z : α), R z ≠ ⊤ := fun R z => by
    have hraw : ∑ y : α, R.1 y = 1 := by
      have := R.2.tsum_eq; rwa [tsum_fintype] at this
    have h1 : R.1 z ≤ 1 :=
      (Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ z)).trans hraw.le
    exact (h1.trans_lt (by norm_num : (1 : ℝ≥0∞) < ⊤)).ne
  have hne_top_K : ∀ (x : α) (y : β), K x y ≠ ⊤ := fun x y => by
    have hraw : ∑ z : β, (K x).1 z = 1 := by
      have := (K x).2.tsum_eq; rwa [tsum_fintype] at this
    have h1 : (K x).1 y ≤ 1 :=
      (Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ y)).trans hraw.le
    exact (h1.trans_lt (by norm_num : (1 : ℝ≥0∞) < ⊤)).ne
  have hbind : ∀ (R : PMF α) (y : β),
      ((R.bind K) y).toReal = ∑ x : α, (R x).toReal * (K x y).toReal := by
    intro R y
    have hne : ∀ x : α, R x * K x y ≠ ⊤ :=
      fun x => ENNReal.mul_ne_top (hne_top R x) (hne_top_K x y)
    calc ((R.bind K) y).toReal
        = (∑ x ∈ Finset.univ, R x * K x y).toReal := by
            congr 1; rw [PMF.bind_apply, tsum_fintype]
      _ = ∑ x ∈ Finset.univ, (R x * K x y).toReal :=
            ENNReal.toReal_sum (fun x _ => hne x)
      _ = ∑ x : α, (R x).toReal * (K x y).toReal :=
            Finset.sum_congr rfl (fun x _ => ENNReal.toReal_mul)
  simp only [tvDist, hbind]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  calc ∑ y : β, |∑ x : α, (P x).toReal * (K x y).toReal
               - ∑ x : α, (Q x).toReal * (K x y).toReal|
      = ∑ y : β, |∑ x : α, ((P x).toReal - (Q x).toReal) * (K x y).toReal| := by
          congr 1; ext y; congr 1
          rw [← Finset.sum_sub_distrib]; congr 1; ext x; ring
    _ ≤ ∑ y : β, ∑ x : α, |(P x).toReal - (Q x).toReal| * (K x y).toReal := by
          apply Finset.sum_le_sum; intro y _
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
          rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
    _ = ∑ x : α, |(P x).toReal - (Q x).toReal| * ∑ y : β, (K x y).toReal := by
          rw [Finset.sum_comm]; congr 1; ext x; rw [← Finset.mul_sum]
    _ = ∑ x : α, |(P x).toReal - (Q x).toReal| := by
          congr 1; ext x; rw [PMF_sum_toReal (K x), mul_one]

end DataProcessingTV

-- §6  AZUMA–HOEFFDING

section AzumaHoeffding

/-- Azuma–Hoeffding martingale tail bound with bounded differences ≤ 1. -/
theorem azuma_hoeffding {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} (f : ℕ → Ω → ℝ)
    (ℱ : MeasureTheory.Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (h_mart : Martingale f ℱ μ)
    (h_bounded : ∀ i ω, |f (i + 1) ω - f i ω| ≤ 1)
    (lam : ℝ) (hlam : 0 ≤ lam) :
    μ {ω | f n ω - f 0 ω ≤ -lam} ≤
      ENNReal.ofReal (Real.exp (-lam ^ 2 / (2 * n))) := by
  rcases eq_or_lt_of_le hlam with rfl | hlam_pos
  · simp only [neg_zero, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
               zero_div, Real.exp_zero, ENNReal.ofReal_one]
    exact prob_le_one
  rcases Nat.eq_zero_or_pos n with rfl | hn_pos
  · simp only [Nat.cast_zero, mul_zero, div_zero, Real.exp_zero, ENNReal.ofReal_one]
    exact prob_le_one
  have hn_pos' : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn_pos
  set t := lam / n with ht_def
  have ht_pos : 0 < t := div_pos hlam_pos hn_pos'
  have hf_sm : ∀ i, StronglyMeasurable (f i) := fun i => (h_mart.1 i).mono (ℱ.le i)
  have h_bound : ∀ m ω, |f m ω - f 0 ω| ≤ (m : ℝ) := by
    intro m; induction m with
    | zero => intro ω; simp
    | succ k ih =>
      intro ω
      have htr : |(f (k + 1) ω - f k ω) + (f k ω - f 0 ω)| ≤
                 |f (k + 1) ω - f k ω| + |f k ω - f 0 ω| := by
        have := norm_add_le (f (k + 1) ω - f k ω) (f k ω - f 0 ω)
        simp only [Real.norm_eq_abs] at this; exact this
      have heq : f (k + 1) ω - f 0 ω = (f (k + 1) ω - f k ω) + (f k ω - f 0 ω) := by ring
      have hmain : |f (k + 1) ω - f 0 ω| ≤ 1 + (k : ℝ) :=
        heq ▸ htr.trans (add_le_add (h_bounded k ω) (ih ω))
      linarith [show ((k + 1 : ℕ) : ℝ) = 1 + k from by push_cast; ring]
  have h_int_exp : ∀ m, Integrable (fun ω => Real.exp (-t * (f m ω - f 0 ω))) μ := by
    intro m
    apply Integrable.mono (integrable_const (Real.exp (t * (m : ℝ))))
    · exact (((hf_sm m).sub (hf_sm 0)).const_mul (-t)).measurable.exp.aestronglyMeasurable
    · filter_upwards with ω
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
          Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      have := (abs_le.mp (h_bound m ω)).1; nlinarith [ht_pos.le]
  have hconv_pw : ∀ (x s : ℝ), |x| ≤ 1 →
      Real.exp (s * x) ≤ (1 + x) / 2 * Real.exp s + (1 - x) / 2 * Real.exp (-s) := by
    intro x s hx
    have hx1 : -1 ≤ x := neg_le_of_abs_le hx
    have hx2 : x ≤ 1 := (abs_le.mp hx).2
    have ha  : 0 ≤ (1 + x) / 2 := by linarith
    have hb  : 0 ≤ (1 - x) / 2 := by linarith
    have hsum : (1 + x) / 2 + (1 - x) / 2 = 1 := by ring
    have hkey : (1 + x) / 2 * s + (1 - x) / 2 * (-s) = s * x := by ring
    have hc := convexOn_exp.2 (Set.mem_univ s) (Set.mem_univ (-s)) ha hb hsum
    simp only [smul_eq_mul] at hc; linarith [hkey ▸ hc]
  have hcosh_le : (Real.exp (-t) + Real.exp t) / 2 ≤ Real.exp (t ^ 2 / 2) := by
    let ν : Measure ℝ :=
      (1 / 2 : ℝ≥0∞) • Measure.dirac (-1 : ℝ) + (1 / 2 : ℝ≥0∞) • Measure.dirac 1
    haveI hν : IsProbabilityMeasure ν := by
      constructor
      simp only [ν, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
                 Measure.dirac_apply_of_mem (Set.mem_univ _), mul_one]
      rw [one_div, ← two_mul]
      exact ENNReal.mul_inv_cancel
        (show (2 : ℝ≥0∞) ≠ 0 from by norm_num)
        (show (2 : ℝ≥0∞) ≠ ⊤ from by norm_num)
    have h_mem : ∀ᵐ x ∂ν, id x ∈ Set.Icc (-1 : ℝ) 1 := by
      rw [ae_iff]; change ν (Set.Icc (-1 : ℝ) 1)ᶜ = 0
      simp only [ν, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
      have h1 : Measure.dirac (-1 : ℝ) (Set.Icc (-1 : ℝ) 1)ᶜ = 0 := by
        have hval := Measure.dirac_apply_of_mem (show (-1 : ℝ) ∈ Set.Icc (-1) 1 by norm_num)
        rw [measure_compl measurableSet_Icc (hval ▸ (by norm_num : (1 : ℝ≥0∞) ≠ ⊤)),
            hval, Measure.dirac_apply_of_mem (Set.mem_univ _)]; simp
      have h2 : Measure.dirac (1 : ℝ) (Set.Icc (-1 : ℝ) 1)ᶜ = 0 := by
        have hval := Measure.dirac_apply_of_mem (show (1 : ℝ) ∈ Set.Icc (-1) 1 by norm_num)
        rw [measure_compl measurableSet_Icc (hval ▸ (by norm_num : (1 : ℝ≥0∞) ≠ ⊤)),
            hval, Measure.dirac_apply_of_mem (Set.mem_univ _)]; simp
      simp [h1, h2]
    have hI_id : ∀ a : ℝ, Integrable (fun x : ℝ => x) (Measure.dirac a) := fun a =>
      ⟨stronglyMeasurable_id.aestronglyMeasurable, by
        show ∫⁻ x, ‖x‖₊ ∂(Measure.dirac a) < ⊤
        simp only [lintegral_dirac]; exact ENNReal.coe_lt_top⟩
    have h_int : ∫ x : ℝ, id x ∂ν = 0 := by
      show ∫ x : ℝ, x ∂ν = 0
      rw [show ν = (1/2 : ℝ≥0∞) • Measure.dirac (-1 : ℝ) +
                   (1/2 : ℝ≥0∞) • Measure.dirac 1 from rfl,
          integral_add_measure
            ((hI_id (-1)).smul_measure (show (1/2 : ℝ≥0∞) ≠ ⊤ from by norm_num))
            ((hI_id 1).smul_measure  (show (1/2 : ℝ≥0∞) ≠ ⊤ from by norm_num)),
          integral_smul_measure, integral_smul_measure,
          integral_dirac, integral_dirac]
      simp only [smul_eq_mul]; ring
    have hSG := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero aemeasurable_id h_mem h_int
    have hexp_sm : StronglyMeasurable (fun x : ℝ => Real.exp ((-t) * x)) :=
      (measurable_const.mul measurable_id).exp.stronglyMeasurable
    have hI_exp : ∀ a : ℝ, Integrable (fun x : ℝ => Real.exp ((-t) * x)) (Measure.dirac a) :=
      fun a => ⟨hexp_sm.aestronglyMeasurable, by
        show ∫⁻ x, ‖Real.exp ((-t) * x)‖₊ ∂(Measure.dirac a) < ⊤
        simp only [lintegral_dirac]; exact ENNReal.coe_lt_top⟩
    have hmgf_val : mgf id ν (-t) = (Real.exp (-t) + Real.exp t) / 2 := by
      simp only [mgf, id]
      rw [show ν = (1/2 : ℝ≥0∞) • Measure.dirac (-1 : ℝ) +
                   (1/2 : ℝ≥0∞) • Measure.dirac 1 from rfl,
          integral_add_measure
            ((hI_exp (-1)).smul_measure (show (1/2 : ℝ≥0∞) ≠ ⊤ from by norm_num))
            ((hI_exp 1).smul_measure  (show (1/2 : ℝ≥0∞) ≠ ⊤ from by norm_num)),
          integral_smul_measure, integral_smul_measure,
          integral_dirac, integral_dirac]
      simp only [mul_neg, neg_neg, mul_one, smul_eq_mul]
      have hc : (1 / 2 : ℝ≥0∞).toReal = 1 / 2 := by
        rw [show (1 / 2 : ℝ≥0∞) = (2 : ℝ≥0∞)⁻¹ from by norm_num,
            ENNReal.toReal_inv, ENNReal.toReal_ofNat]
        norm_num
      simp only [hc]; ring
    have hmgf_ineq := hSG.mgf_le (-t)
    rw [hmgf_val] at hmgf_ineq
    calc (Real.exp (-t) + Real.exp t) / 2
        ≤ Real.exp ((↑(‖(1 : ℝ) - (-1 : ℝ)‖₊ / 2) : ℝ) ^ 2 * (-t) ^ 2 / 2) := hmgf_ineq
      _ = Real.exp (t ^ 2 / 2) := by congr 1; push_cast; norm_num
  have h_cond_mgf : ∀ k, ∀ᵐ ω ∂μ,
      μ[fun ω' => Real.exp (-t * (f (k + 1) ω' - f k ω')) | ℱ k] ω ≤ Real.exp (t ^ 2 / 2) := by
    intro k
    have h_pw : ∀ ω, Real.exp (-t * (f (k + 1) ω - f k ω)) ≤
        (1 + (f (k + 1) ω - f k ω)) / 2 * Real.exp (-t) +
        (1 - (f (k + 1) ω - f k ω)) / 2 * Real.exp t := by
      intro ω
      have h := hconv_pw (f (k + 1) ω - f k ω) (-t) (h_bounded k ω)
      ring_nf at h ⊢; linarith
    have hd_int : Integrable (fun ω => f (k + 1) ω - f k ω) μ :=
      (h_mart.integrable (k + 1)).sub (h_mart.integrable k)
    have hbdd_int : Integrable (fun ω =>
        (1 + (f (k + 1) ω - f k ω)) / 2 * Real.exp (-t) +
        (1 - (f (k + 1) ω - f k ω)) / 2 * Real.exp t) μ :=
      ((((integrable_const 1).add hd_int).div_const 2).mul_const _).add
        (((integrable_const 1).sub hd_int |>.div_const 2).mul_const _)
    have hexp_step_aesm : AEStronglyMeasurable
        (fun ω => Real.exp (-t * (f (k + 1) ω - f k ω))) μ :=
      (((hf_sm (k + 1)).sub (hf_sm k)).const_mul (-t)).measurable.exp.aestronglyMeasurable
    have hexp_int : Integrable (fun ω => Real.exp (-t * (f (k + 1) ω - f k ω))) μ := by
      apply Integrable.mono hbdd_int hexp_step_aesm
      filter_upwards with ω
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.norm_eq_abs]
      have h1 : 0 ≤ (1 + (f (k + 1) ω - f k ω)) / 2 := by
        have := (abs_le.mp (h_bounded k ω)).1; linarith
      have h2 : 0 ≤ (1 - (f (k + 1) ω - f k ω)) / 2 := by
        have := (abs_le.mp (h_bounded k ω)).2; linarith
      have hpos : 0 < (1 + (f (k + 1) ω - f k ω)) / 2 * Real.exp (-t) +
                     (1 - (f (k + 1) ω - f k ω)) / 2 * Real.exp t :=
        calc 0 < Real.exp (-t) := Real.exp_pos _
          _ = ((1 + (f (k + 1) ω - f k ω)) / 2 +
               (1 - (f (k + 1) ω - f k ω)) / 2) * Real.exp (-t) := by ring
          _ = (1 + (f (k + 1) ω - f k ω)) / 2 * Real.exp (-t) +
              (1 - (f (k + 1) ω - f k ω)) / 2 * Real.exp (-t) := by ring
          _ ≤ (1 + (f (k + 1) ω - f k ω)) / 2 * Real.exp (-t) +
              (1 - (f (k + 1) ω - f k ω)) / 2 * Real.exp t := by
              have hexp : Real.exp (-t) ≤ Real.exp t := Real.exp_le_exp.mpr (by linarith)
              linarith [mul_le_mul_of_nonneg_left hexp h2]
      rw [abs_of_pos hpos]; linarith [h_pw ω]
    have h_mono := condExp_mono (m := ℱ k) hexp_int hbdd_int
      (Filter.Eventually.of_forall h_pw)
    have hmart_cond : μ[fun ω' => f (k + 1) ω' - f k ω' | ℱ k] =ᵐ[μ] fun _ => (0 : ℝ) := by
      have h1 := h_mart.2 k (k + 1) (Nat.le_succ k)
      have h2 := condExp_of_stronglyMeasurable (ℱ.le k) (h_mart.1 k) (h_mart.integrable k)
      have h3 : μ[fun ω' => f (k + 1) ω' - f k ω' | ℱ k] =ᵐ[μ]
                fun ω => μ[f (k + 1) | (ℱ k : MeasurableSpace Ω)] ω -
                         μ[f k | (ℱ k : MeasurableSpace Ω)] ω := by
        filter_upwards [condExp_sub (h_mart.integrable (k + 1)) (h_mart.integrable k) (ℱ k)]
          with ω h
        simp only [Pi.sub_apply] at h
        exact h
      filter_upwards [h1, h3] with ω hfk1 hd
      have hfk2 := congr_fun h2 ω
      linarith
    have hcondexp_rhs : μ[fun ω' =>
        (1 + (f (k + 1) ω' - f k ω')) / 2 * Real.exp (-t) +
        (1 - (f (k + 1) ω' - f k ω')) / 2 * Real.exp t | ℱ k]
        =ᵐ[μ] fun _ => (Real.exp (-t) + Real.exp t) / 2 := by
      have heq : (fun ω' =>
          (1 + (f (k + 1) ω' - f k ω')) / 2 * Real.exp (-t) +
          (1 - (f (k + 1) ω' - f k ω')) / 2 * Real.exp t) = fun ω' =>
          (Real.exp (-t) + Real.exp t) / 2 +
          (Real.exp (-t) - Real.exp t) / 2 * (f (k + 1) ω' - f k ω') := by ext ω'; ring
      rw [heq]
      have hadd := condExp_add (m := ℱ k)
        (integrable_const ((Real.exp (-t) + Real.exp t) / 2))
        (hd_int.const_mul ((Real.exp (-t) - Real.exp t) / 2))
      have hconst := condExp_const (μ := μ) (ℱ.le k) ((Real.exp (-t) + Real.exp t) / 2)
      have hsmul := condExp_smul (μ := μ) ((Real.exp (-t) - Real.exp t) / 2)
        (fun ω' => f (k + 1) ω' - f k ω') (ℱ k)
      filter_upwards [hadd, hsmul, hmart_cond] with ω h1 h3 h4
      have h2 := congr_fun hconst ω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at *
      have hb1 : μ[((Real.exp (-t) - Real.exp t) / 2) • fun ω' => f (k + 1) ω' - f k ω' |
                   (ℱ k : MeasurableSpace Ω)] ω =
                 μ[fun x => (Real.exp (-t) - Real.exp t) / 2 * (f (k + 1) x - f k x) |
                   (ℱ k : MeasurableSpace Ω)] ω := rfl
      have hb2 : μ[fun ω' => (Real.exp (-t) + Real.exp t) / 2 +
                              (Real.exp (-t) - Real.exp t) / 2 * (f (k + 1) ω' - f k ω') |
                   (ℱ k : MeasurableSpace Ω)] ω =
                 μ[(fun x => (Real.exp (-t) + Real.exp t) / 2) +
                   fun x => (Real.exp (-t) - Real.exp t) / 2 * (f (k + 1) x - f k x) |
                   (ℱ k : MeasurableSpace Ω)] ω := rfl
      have hBF : ((Real.exp (-t) - Real.exp t) / 2) * μ[fun ω' => f (k + 1) ω' - f k ω' | (ℱ k : MeasurableSpace Ω)] ω = 0 := by
        rw [h4, mul_zero]
      linarith [h1.symm, h2.symm, h3.symm, h4, hb1, hb2, hBF]
    filter_upwards [h_mono, hcondexp_rhs] with ω hle heq
    calc μ[fun ω' => Real.exp (-t * (f (k + 1) ω' - f k ω')) | ℱ k] ω
        ≤ μ[fun ω' =>
            (1 + (f (k + 1) ω' - f k ω')) / 2 * Real.exp (-t) +
            (1 - (f (k + 1) ω' - f k ω')) / 2 * Real.exp t | ℱ k] ω := hle
      _ = (Real.exp (-t) + Real.exp t) / 2 := heq
      _ ≤ Real.exp (t ^ 2 / 2) := hcosh_le
  have h_mgf_bound : ∀ m : ℕ, ∫ ω, Real.exp (-t * (f m ω - f 0 ω)) ∂μ ≤
      Real.exp ((m : ℝ) * t ^ 2 / 2) := by
    intro m; induction m with
    | zero => simp
    | succ k ih =>
      have h_meas_k : StronglyMeasurable[ℱ k]
          (fun ω => Real.exp (-t * (f k ω - f 0 ω))) := by
        apply Measurable.stronglyMeasurable
        exact (((h_mart.1 k).measurable.sub
          ((h_mart.1 0).mono (ℱ.mono (Nat.zero_le k))).measurable).const_mul (-t)).exp
      have h_step_int : Integrable (fun ω => Real.exp (-t * (f (k + 1) ω - f k ω))) μ := by
        apply Integrable.mono (integrable_const (Real.exp t))
        · exact (((hf_sm (k + 1)).sub (hf_sm k)).const_mul (-t)).measurable.exp
                |>.aestronglyMeasurable
        · filter_upwards with ω
          rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
              Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
          apply Real.exp_le_exp.mpr
          have := (abs_le.mp (h_bounded k ω)).1; nlinarith [ht_pos.le]
      have h_int_prod : Integrable (fun ω =>
          Real.exp (-t * (f k ω - f 0 ω)) * Real.exp (-t * (f (k + 1) ω - f k ω))) μ := by
        have heq : ∀ ω, Real.exp (-t * (f k ω - f 0 ω)) * Real.exp (-t * (f (k + 1) ω - f k ω)) =
                        Real.exp (-t * (f (k + 1) ω - f 0 ω)) := fun ω => by
          rw [← Real.exp_add]; congr 1; ring
        simp_rw [heq]; exact h_int_exp (k + 1)
      have hnn_cE : 0 ≤ᶠ[ae μ]
          μ[fun ω' => Real.exp (-t * (f (k + 1) ω' - f k ω')) | ℱ k] :=
        condExp_nonneg (ae_of_all μ fun _ => (Real.exp_pos _).le)
      have hcE_int : Integrable
          (μ[fun ω' => Real.exp (-t * (f (k + 1) ω' - f k ω')) | ℱ k]) μ :=
        integrable_condExp
      have h_int_cond_prod : Integrable (fun ω =>
          Real.exp (-t * (f k ω - f 0 ω)) *
          μ[fun ω' => Real.exp (-t * (f (k + 1) ω' - f k ω')) | ℱ k] ω) μ := by
        apply Integrable.mono ((h_int_exp k).mul_const (Real.exp (t ^ 2 / 2)))
        · exact (h_meas_k.mono (ℱ.le k)).aestronglyMeasurable.mul hcE_int.aestronglyMeasurable
        · filter_upwards [h_cond_mgf k, hnn_cE] with ω hle hnn
          simp only [norm_mul, Real.norm_of_nonneg hnn,
                     Real.norm_of_nonneg (Real.exp_pos _).le]
          exact mul_le_mul_of_nonneg_left hle (Real.exp_pos _).le
      rw [show ((k.succ : ℝ)) * t ^ 2 / 2 = t ^ 2 / 2 + (k : ℝ) * t ^ 2 / 2 by
              push_cast; ring, Real.exp_add]
      calc ∫ ω, Real.exp (-t * (f (k + 1) ω - f 0 ω)) ∂μ
          = ∫ ω, Real.exp (-t * (f k ω - f 0 ω)) *
                Real.exp (-t * (f (k + 1) ω - f k ω)) ∂μ := by
              congr 1; ext ω; rw [← Real.exp_add]; congr 1; ring
        _ = ∫ ω, Real.exp (-t * (f k ω - f 0 ω)) *
                μ[fun ω' => Real.exp (-t * (f (k + 1) ω' - f k ω')) | ℱ k] ω ∂μ := by
              rw [← integral_condExp (ℱ.le k)]
              apply integral_congr_ae
              exact condExp_mul_of_stronglyMeasurable_left h_meas_k h_int_prod h_step_int
        _ ≤ ∫ ω, Real.exp (-t * (f k ω - f 0 ω)) * Real.exp (t ^ 2 / 2) ∂μ :=
              integral_mono_ae h_int_cond_prod ((h_int_exp k).mul_const _)
                (by filter_upwards [h_cond_mgf k] with ω hle
                    exact mul_le_mul_of_nonneg_left hle (Real.exp_pos _).le)
        _ = Real.exp (t ^ 2 / 2) * ∫ ω, Real.exp (-t * (f k ω - f 0 ω)) ∂μ := by
              have hsmul_conv : ∀ ω : Ω,
                  Real.exp (-t * (f k ω - f 0 ω)) * Real.exp (t ^ 2 / 2) =
                  Real.exp (t ^ 2 / 2) • Real.exp (-t * (f k ω - f 0 ω)) :=
                fun ω => by rw [smul_eq_mul]; ring
              simp_rw [hsmul_conv]
              rw [integral_smul (Real.exp (t ^ 2 / 2))]
              simp only [smul_eq_mul]
        _ ≤ Real.exp (t ^ 2 / 2) * Real.exp ((k : ℝ) * t ^ 2 / 2) :=
              mul_le_mul_of_nonneg_left ih (Real.exp_pos _).le
  have h_final : μ.real {ω | f n ω - f 0 ω ≤ -lam} ≤ Real.exp (-lam ^ 2 / (2 * n)) := by
    have h_sub : {ω | f n ω - f 0 ω ≤ -lam} ⊆
        {ω | Real.exp (t * lam) ≤ Real.exp (-t * (f n ω - f 0 ω))} := by
      intro ω hω; simp only [Set.mem_setOf_eq] at *; rw [Real.exp_le_exp]; nlinarith
    have hnn : 0 ≤ᶠ[ae μ] fun ω => Real.exp (-t * (f n ω - f 0 ω)) :=
      ae_of_all μ fun ω => (Real.exp_pos _).le
    have hM := (mul_meas_ge_le_integral_of_nonneg hnn (h_int_exp n)) (Real.exp (t * lam))
    calc μ.real {ω | f n ω - f 0 ω ≤ -lam}
        ≤ μ.real {ω | Real.exp (t * lam) ≤ Real.exp (-t * (f n ω - f 0 ω))} :=
              measureReal_mono h_sub (measure_ne_top μ _)
      _ = (Real.exp (t * lam))⁻¹ *
              (Real.exp (t * lam) *
               μ.real {ω | Real.exp (t * lam) ≤ Real.exp (-t * (f n ω - f 0 ω))}) := by
              rw [← mul_assoc, inv_mul_cancel₀ (Real.exp_pos _).ne', one_mul]
      _ ≤ (Real.exp (t * lam))⁻¹ * ∫ ω, Real.exp (-t * (f n ω - f 0 ω)) ∂μ :=
              mul_le_mul_of_nonneg_left hM (inv_nonneg.mpr (Real.exp_pos _).le)
      _ ≤ (Real.exp (t * lam))⁻¹ * Real.exp ((n : ℝ) * t ^ 2 / 2) :=
              mul_le_mul_of_nonneg_left (h_mgf_bound n) (inv_nonneg.mpr (Real.exp_pos _).le)
      _ = Real.exp (-lam ^ 2 / (2 * n)) := by
              rw [ht_def, ← Real.exp_neg, ← Real.exp_add]; congr 1; field_simp; ring
  rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
  exact ENNReal.ofReal_le_ofReal h_final

end AzumaHoeffding

-- §7  KRONECKER'S LEMMA

section Kronecker

lemma kronecker_lemma {a b : ℕ → ℝ}
    (hb_pos  : ∀ n, 0 < b n)
    (hb_mono : Monotone b)
    (hb_div  : Tendsto b atTop atTop)
    (hsum    : Summable (fun n => a n / b n)) :
    Tendsto (fun n => (1 / b n) * ∑ k ∈ Finset.range n, a k) atTop (𝓝 0) := by
  have hb_ne     : ∀ n, b n ≠ 0     := fun n => (hb_pos n).ne'
  have hb_nonneg : ∀ n, 0 ≤ b n     := fun n => (hb_pos n).le
  have hw_nn : ∀ k, 0 ≤ b (k + 1) - b k :=
    fun k => sub_nonneg.mpr (hb_mono (Nat.le_succ k))
  set S := ∑' n, (a n / b n)
  have hS : HasSum (fun n => a n / b n) S := hsum.hasSum
  set R : ℕ → ℝ := fun n => S - ∑ k ∈ Finset.range n, (a k / b k) with hR_def
  have hR : Tendsto R atTop (𝓝 0) := by
    have hpart := hS.tendsto_sum_nat
    have hconst : Tendsto (fun _ : ℕ => S) atTop (𝓝 S) := tendsto_const_nhds
    simpa [sub_self] using hconst.sub hpart
  have hR_rec : ∀ n, R (n + 1) = R n - a n / b n := by
    intro n
    simp only [hR_def, Finset.sum_range_succ]
    ring
  have hSBP : ∀ n, ∑ k ∈ Finset.range n, a k =
      b 0 * R 0 - b n * R n +
      ∑ k ∈ Finset.range n, (b (k + 1) - b k) * R (k + 1) := by
    intro n
    induction n with
    | zero => simp [hR_def]
    | succ n ih =>
      simp only [Finset.sum_range_succ]
      rw [hR_rec n, ih]
      field_simp [hb_ne n]
      ring
  have hcongr : ∀ n,
      (1 / b n) * ∑ k ∈ Finset.range n, a k =
        b 0 * R 0 / b n - R n +
        (1 / b n) * ∑ k ∈ Finset.range n, (b (k + 1) - b k) * R (k + 1) := by
    intro n
    rw [hSBP n]
    field_simp [hb_ne n]
  have h_inv_b : Tendsto (fun n => (b n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hb_div
  have h1 : Tendsto (fun n => b 0 * R 0 / b n) atTop (𝓝 0) := by
    have hmul : Tendsto (fun n => b 0 * R 0 * (b n)⁻¹) atTop (𝓝 (b 0 * R 0 * 0)) :=
      tendsto_const_nhds.mul h_inv_b
    simp only [mul_zero] at hmul
    exact hmul.congr (fun n => (div_eq_mul_inv _ _).symm)
  have h_cesaro : Tendsto
      (fun n => (1 / b n) * ∑ k ∈ Finset.range n, (b (k + 1) - b k) * R (k + 1))
      atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    rw [Metric.tendsto_atTop] at hR
    obtain ⟨N, hN⟩ := hR (ε / 2) (half_pos hε)
    set C := ∑ k ∈ Finset.range (N + 1), (b (k + 1) - b k) * |R (k + 1)|
    have hC_nn : 0 ≤ C := Finset.sum_nonneg fun k _ =>
      mul_nonneg (hw_nn k) (abs_nonneg _)
    have hCbn : Tendsto (fun n => C / b n) atTop (𝓝 0) := by
      have hmul : Tendsto (fun n => C * (b n)⁻¹) atTop (𝓝 (C * 0)) :=
        tendsto_const_nhds.mul h_inv_b
      simp only [mul_zero] at hmul
      exact hmul.congr (fun n => (div_eq_mul_inv _ _).symm)
    obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp hCbn (ε / 2) (half_pos hε)
    refine ⟨max (N + 2) M, fun n hn => ?_⟩
    have hn_N1 : N + 1 < n := by
      have h : N + 2 ≤ n := (le_max_left _ _).trans hn
      omega
    have hn_M : M ≤ n := (le_max_right _ _).trans hn
    have hbn_pos : 0 < b n       := hb_pos n
    have h1bn_nn : (0 : ℝ) ≤ 1 / b n := by positivity
    have hdisj : Disjoint (Finset.range (N + 1)) (Finset.Ico (N + 1) n) :=
      Finset.disjoint_left.mpr fun x hx1 hx2 => by
        simp only [Finset.mem_range] at hx1
        simp only [Finset.mem_Ico] at hx2
        omega
    have hcov : Finset.range n = Finset.range (N + 1) ∪ Finset.Ico (N + 1) n := by
      ext k
      simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
      omega
    have htelescope : ∑ k ∈ Finset.Ico (N + 1) n, (b (k + 1) - b k) = b n - b (N + 1) := by
      have hA : ∑ k ∈ Finset.range n, (b (k + 1) - b k) = b n - b 0 :=
        Finset.sum_range_sub (f := b) n
      have hB : ∑ k ∈ Finset.range (N + 1), (b (k + 1) - b k) = b (N + 1) - b 0 :=
        Finset.sum_range_sub (f := b) (N + 1)
      have hC_split : ∑ k ∈ Finset.range n, (b (k + 1) - b k) =
          ∑ k ∈ Finset.range (N + 1), (b (k + 1) - b k) +
          ∑ k ∈ Finset.Ico (N + 1) n, (b (k + 1) - b k) := by
        rw [← Finset.sum_union hdisj, ← hcov]
      linarith
    have hS_late : |∑ k ∈ Finset.Ico (N + 1) n, (b (k + 1) - b k) * R (k + 1)| ≤
        ε / 2 * (b n - b (N + 1)) :=
      calc |∑ k ∈ Finset.Ico (N + 1) n, (b (k + 1) - b k) * R (k + 1)|
          ≤ ∑ k ∈ Finset.Ico (N + 1) n, (b (k + 1) - b k) * |R (k + 1)| := by
              refine (Finset.abs_sum_le_sum_abs _ _).trans_eq ?_
              apply Finset.sum_congr rfl; intro k _
              rw [abs_mul, abs_of_nonneg (hw_nn k)]
        _ ≤ ∑ k ∈ Finset.Ico (N + 1) n, (b (k + 1) - b k) * (ε / 2) := by
              apply Finset.sum_le_sum; intro k hk
              apply mul_le_mul_of_nonneg_left _ (hw_nn k)
              have h' := hN (k + 1) (by
                have := (Finset.mem_Ico.mp hk).1; omega)
              rw [dist_zero_right, Real.norm_eq_abs] at h'
              exact h'.le
        _ = ε / 2 * (b n - b (N + 1)) := by
              rw [show ∑ k ∈ Finset.Ico (N + 1) n, (b (k + 1) - b k) * (ε / 2) =
                      ε / 2 * ∑ k ∈ Finset.Ico (N + 1) n, (b (k + 1) - b k) from by
                rw [Finset.mul_sum]; congr 1; ext k; ring,
                htelescope]
    have hS_early : |∑ k ∈ Finset.range (N + 1), (b (k + 1) - b k) * R (k + 1)| ≤ C :=
      (Finset.abs_sum_le_sum_abs _ _).trans_eq
        (Finset.sum_congr rfl fun k _ => by rw [abs_mul, abs_of_nonneg (hw_nn k)])
    rw [hcov, Finset.sum_union hdisj, dist_zero_right, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg h1bn_nn]
    calc 1 / b n *
          |∑ k ∈ Finset.range (N + 1), (b (k + 1) - b k) * R (k + 1) +
           ∑ k ∈ Finset.Ico (N + 1) n, (b (k + 1) - b k) * R (k + 1)|
        ≤ 1 / b n * (C + ε / 2 * (b n - b (N + 1))) := by
            apply mul_le_mul_of_nonneg_left _ h1bn_nn
            have htr := norm_add_le
              (∑ k ∈ Finset.range (N + 1), (b (k + 1) - b k) * R (k + 1))
              (∑ k ∈ Finset.Ico (N + 1) n, (b (k + 1) - b k) * R (k + 1))
            simp only [Real.norm_eq_abs] at htr
            exact htr.trans (add_le_add hS_early hS_late)
      _ = C / b n + ε / 2 * (1 - b (N + 1) / b n) := by
            field_simp [hb_ne n]
      _ ≤ C / b n + ε / 2 := by
            have hrat : 0 ≤ b (N + 1) / b n := div_nonneg (hb_nonneg _) hbn_pos.le
            nlinarith [half_pos hε]
      _ < ε / 2 + ε / 2 := by
            have hMn := hM n hn_M
            rw [dist_zero_right, Real.norm_eq_abs,
                abs_of_nonneg (div_nonneg hC_nn hbn_pos.le)] at hMn
            linarith
      _ = ε := by ring
  have h12 : Tendsto (fun n => b 0 * R 0 / b n - R n) atTop (𝓝 0) := by
    have := h1.sub hR; simpa using this
  have h123 : Tendsto (fun n => b 0 * R 0 / b n - R n +
      (1 / b n) * ∑ k ∈ Finset.range n, (b (k + 1) - b k) * R (k + 1)) atTop (𝓝 0) := by
    have := h12.add h_cesaro; simpa using this
  exact h123.congr (fun n => (hcongr n).symm)

end Kronecker

-- §8  JSD IDENTITY AND UPPER BOUND

section JSD

noncomputable def JSD {α : Type*} [Fintype α] (P Q : PMF α) : ℝ :=
  (1 / 2) * klDiv P (mixPMF P Q) + (1 / 2) * klDiv Q (mixPMF P Q)

lemma log_sum_inequality {a₁ a₂ b₁ b₂ : ℝ}
    (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) :
    a₁ * Real.log (a₁ / b₁) + a₂ * Real.log (a₂ / b₂) ≥
    (a₁ + a₂) * Real.log ((a₁ + a₂) / (b₁ + b₂)) := by
  have hT : 0 < b₁ + b₂ := by linarith
  rcases eq_or_lt_of_le ha₁ with rfl | ha₁'
  · simp only [zero_mul, zero_add]
    rcases eq_or_lt_of_le ha₂ with rfl | ha₂'
    · simp
    · apply mul_le_mul_of_nonneg_left _ ha₂'.le
      apply Real.log_le_log (div_pos ha₂' hT)
      gcongr; linarith
  rcases eq_or_lt_of_le ha₂ with rfl | ha₂'
  · simp only [zero_mul, add_zero]
    rcases eq_or_lt_of_le ha₁ with rfl | ha₁''
    · simp
    · apply mul_le_mul_of_nonneg_left _ ha₁'.le
      apply Real.log_le_log (div_pos ha₁' hT)
      gcongr; linarith
  have hS : 0 < a₁ + a₂ := by linarith
  rw [ge_iff_le, ← sub_nonneg]
  have lhs_rhs : a₁ * Real.log (a₁ / b₁) + a₂ * Real.log (a₂ / b₂) -
                 (a₁ + a₂) * Real.log ((a₁ + a₂) / (b₁ + b₂)) =
                 a₁ * Real.log (a₁ * (b₁ + b₂) / (b₁ * (a₁ + a₂))) +
                 a₂ * Real.log (a₂ * (b₁ + b₂) / (b₂ * (a₁ + a₂))) := by
    rw [Real.log_div ha₁'.ne' hb₁.ne', Real.log_div ha₂'.ne' hb₂.ne',
        Real.log_div hS.ne' hT.ne',
        Real.log_div (mul_pos ha₁' hT).ne' (mul_pos hb₁ hS).ne',
        Real.log_div (mul_pos ha₂' hT).ne' (mul_pos hb₂ hS).ne',
        Real.log_mul ha₁'.ne' hT.ne', Real.log_mul hb₁.ne' hS.ne',
        Real.log_mul ha₂'.ne' hT.ne', Real.log_mul hb₂.ne' hS.ne']
    ring
  rw [lhs_rhs]
  have hlog₁ : Real.log (a₁ * (b₁ + b₂) / (b₁ * (a₁ + a₂))) ≥
               1 - b₁ * (a₁ + a₂) / (a₁ * (b₁ + b₂)) := by
    have hinv := log_le_sub_one (by positivity : 0 < b₁ * (a₁ + a₂) / (a₁ * (b₁ + b₂)))
    have heq : Real.log (b₁ * (a₁ + a₂) / (a₁ * (b₁ + b₂))) =
               -Real.log (a₁ * (b₁ + b₂) / (b₁ * (a₁ + a₂))) := by
      rw [Real.log_div (mul_pos hb₁ hS).ne' (mul_pos ha₁' hT).ne',
          Real.log_div (mul_pos ha₁' hT).ne' (mul_pos hb₁ hS).ne']; ring
    linarith [heq ▸ hinv]
  have hlog₂ : Real.log (a₂ * (b₁ + b₂) / (b₂ * (a₁ + a₂))) ≥
               1 - b₂ * (a₁ + a₂) / (a₂ * (b₁ + b₂)) := by
    have hinv := log_le_sub_one (by positivity : 0 < b₂ * (a₁ + a₂) / (a₂ * (b₁ + b₂)))
    have heq : Real.log (b₂ * (a₁ + a₂) / (a₂ * (b₁ + b₂))) =
               -Real.log (a₂ * (b₁ + b₂) / (b₂ * (a₁ + a₂))) := by
      rw [Real.log_div (mul_pos hb₂ hS).ne' (mul_pos ha₂' hT).ne',
          Real.log_div (mul_pos ha₂' hT).ne' (mul_pos hb₂ hS).ne']; ring
    linarith [heq ▸ hinv]
  have bound₁ : a₁ * Real.log (a₁ * (b₁ + b₂) / (b₁ * (a₁ + a₂))) ≥
                a₁ - b₁ * (a₁ + a₂) / (b₁ + b₂) := by
    have h := mul_le_mul_of_nonneg_left hlog₁ ha₁'.le
    have eq : a₁ * (1 - b₁ * (a₁ + a₂) / (a₁ * (b₁ + b₂))) =
              a₁ - b₁ * (a₁ + a₂) / (b₁ + b₂) := by field_simp [ha₁'.ne', hT.ne']
    linarith [eq ▸ h]
  have bound₂ : a₂ * Real.log (a₂ * (b₁ + b₂) / (b₂ * (a₁ + a₂))) ≥
                a₂ - b₂ * (a₁ + a₂) / (b₁ + b₂) := by
    have h := mul_le_mul_of_nonneg_left hlog₂ ha₂'.le
    have eq : a₂ * (1 - b₂ * (a₁ + a₂) / (a₂ * (b₁ + b₂))) =
              a₂ - b₂ * (a₁ + a₂) / (b₁ + b₂) := by field_simp [ha₂'.ne', hT.ne']
    linarith [eq ▸ h]
  have sum_zero : a₁ - b₁ * (a₁ + a₂) / (b₁ + b₂) +
                  (a₂ - b₂ * (a₁ + a₂) / (b₁ + b₂)) = 0 := by
    field_simp [hT.ne']; ring
  linarith

private lemma klDiv_self_eq_zero {α : Type*} [Fintype α] (P : PMF α) :
    klDiv P P = 0 := by
  simp only [klDiv]
  apply Finset.sum_eq_zero
  intro x _
  rcases eq_or_ne ((P x).toReal) 0 with h | h
  · simp [h]
  · rw [div_self h, Real.log_one, mul_zero]

theorem jsd_le_quarter_kl_sym {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (P Q : PMF α)
    (h_ac  : ∀ x, (P x).toReal = 0 ∨ (Q x).toReal > 0)
    (h_ac' : ∀ x, (Q x).toReal = 0 ∨ (P x).toReal > 0) :
    JSD P Q ≤ (1 / 4) * (klDiv P Q + klDiv Q P) := by
  have hPne : ∀ x : α, P.1 x ≠ ⊤ := fun x => by
    have hraw : ∑ y : α, P.1 y = 1 := by
      have := P.2.tsum_eq; rwa [tsum_fintype] at this
    have h1 : P.1 x ≤ 1 :=
      (Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ x)).trans_eq hraw
    exact (h1.trans_lt (by norm_num : (1 : ℝ≥0∞) < ⊤)).ne
  have hQne : ∀ x : α, Q.1 x ≠ ⊤ := fun x => by
    have hraw : ∑ y : α, Q.1 y = 1 := by
      have := Q.2.tsum_eq; rwa [tsum_fintype] at this
    have h1 : Q.1 x ≤ 1 :=
      (Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ x)).trans_eq hraw
    exact (h1.trans_lt (by norm_num : (1 : ℝ≥0∞) < ⊤)).ne
  have hMx : ∀ x : α, (mixPMF P Q x).toReal = ((P x).toReal + (Q x).toReal) / 2 := by
    intro x
    have hPx : (P x : ℝ≥0∞) ≠ ⊤ := hPne x
    have hQx : (Q x : ℝ≥0∞) ≠ ⊤ := hQne x
    show ((P x + Q x) / 2 : ℝ≥0∞).toReal = ((P x).toReal + (Q x).toReal) / 2
    rw [ENNReal.toReal_div, ENNReal.toReal_add hPx hQx]
    norm_num
  have hkl1 : klDiv P (mixPMF P Q) ≤ (1 / 2) * klDiv P Q := by
    simp only [klDiv]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x _
    rw [hMx x]
    rcases eq_or_ne ((P x).toReal) 0 with hP0 | hPne'
    · simp [hP0]
    · have hPpos : 0 < (P x).toReal :=
        lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hPne')
      have hQpos : 0 < (Q x).toReal := by
        rcases h_ac x with h | h
        · exact absurd h hPne'
        · exact h
      have hLSI := log_sum_inequality (le_of_lt hPpos) (le_of_lt hPpos) hPpos hQpos
      rw [div_self (ne_of_gt hPpos), Real.log_one, mul_zero, zero_add] at hLSI
      have hratio : (P x).toReal / (((P x).toReal + (Q x).toReal) / 2) =
                    ((P x).toReal + (P x).toReal) / ((P x).toReal + (Q x).toReal) := by
        field_simp; ring
      rw [hratio]
      have hstep : ((P x).toReal + (P x).toReal) *
                   Real.log (((P x).toReal + (P x).toReal) / ((P x).toReal + (Q x).toReal)) =
                   2 * ((P x).toReal *
                   Real.log (((P x).toReal + (P x).toReal) / ((P x).toReal + (Q x).toReal))) := by
        ring
      rw [hstep] at hLSI
      linarith
  have hkl2 : klDiv Q (mixPMF P Q) ≤ (1 / 2) * klDiv Q P := by
    simp only [klDiv]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x _
    rw [hMx x]
    rcases eq_or_ne ((Q x).toReal) 0 with hQ0 | hQne'
    · simp [hQ0]
    · have hQpos : 0 < (Q x).toReal :=
        lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hQne')
      have hPpos : 0 < (P x).toReal := by
        rcases h_ac' x with h | h
        · exact absurd h hQne'
        · exact h
      have hLSI := log_sum_inequality (le_of_lt hQpos) (le_of_lt hQpos) hQpos hPpos
      rw [div_self (ne_of_gt hQpos), Real.log_one, mul_zero, zero_add] at hLSI
      have hratio : (Q x).toReal / (((P x).toReal + (Q x).toReal) / 2) =
                    ((Q x).toReal + (Q x).toReal) / ((Q x).toReal + (P x).toReal) := by
        field_simp; ring
      rw [hratio]
      have hstep : ((Q x).toReal + (Q x).toReal) *
                   Real.log (((Q x).toReal + (Q x).toReal) / ((Q x).toReal + (P x).toReal)) =
                   2 * ((Q x).toReal *
                   Real.log (((Q x).toReal + (Q x).toReal) / ((Q x).toReal + (P x).toReal))) := by
        ring
      rw [hstep] at hLSI
      linarith
  simp only [JSD]
  linarith

end JSD

-- §9  BERNOULLI KL BOUNDS

section BernoulliKL

noncomputable def klBern (p q : ℝ) : ℝ :=
  p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q))

/-- KL(Bern(p) ‖ Bern(q)) ≥ 2(p − q)².
    Let φ(t) = KL(Bern(t) ‖ Bern(q)) − 2(t−q)². Then φ(q) = 0, φ'(q) = 0,
    and φ''(t) = 1/(t(1−t)) − 4 ≥ 0, so φ is convex with global minimum 0. -/
theorem bernoulli_kl_lower_bound (p q : ℝ)
    (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 < q) (hq1 : q < 1) :
    klBern p q ≥ 2 * (p - q) ^ 2 := by
  simp only [klBern]
  rw [ge_iff_le, ← sub_nonneg]
  have h1p : 0 < 1 - p := by linarith
  have h1q : 0 < 1 - q := by linarith
  set φ : ℝ → ℝ := fun t =>
    t * Real.log (t / q) + (1 - t) * Real.log ((1 - t) / (1 - q)) - 2 * (t - q) ^ 2
  suffices h : 0 ≤ φ p by simpa [φ] using h
  have hφq : φ q = 0 := by
    simp only [φ, div_self hq0.ne', div_self h1q.ne', Real.log_one, mul_zero,
               add_zero, sub_self, sq, mul_zero]
  set φ' : ℝ → ℝ := fun t =>
    Real.log (t / q) - Real.log ((1 - t) / (1 - q)) - 4 * (t - q)
  have hφ_deriv : ∀ t ∈ Set.Ioo 0 1, HasDerivAt φ (φ' t) t := by
    intro t ⟨ht0, ht1⟩
    have h1t : 0 < 1 - t := by linarith
    have hd1 : HasDerivAt (fun u => u * Real.log (u / q)) (Real.log (t / q) + 1) t := by
      have h1 := hasDerivAt_id t
      have h2 : HasDerivAt (fun u => Real.log (u / q)) t⁻¹ t := by
        have hc := (Real.hasDerivAt_log (div_pos ht0 hq0).ne').comp t (h1.div_const q)
        convert hc using 1; field_simp [ht0.ne', hq0.ne']
      convert h1.mul h2 using 1
      simp only [id]; field_simp [ht0.ne']
    have hd2 : HasDerivAt (fun u => (1 - u) * Real.log ((1 - u) / (1 - q)))
               (-(Real.log ((1 - t) / (1 - q)) + 1)) t := by
      have hg : HasDerivAt (fun u : ℝ => 1 - u) (-1) t := by
        have h := (hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)
        convert h using 1; norm_num
      have hf : HasDerivAt (fun u => Real.log ((1 - u) / (1 - q))) (-(1 - t)⁻¹) t := by
        have hc := (Real.hasDerivAt_log (div_pos h1t h1q).ne').comp t (hg.div_const (1 - q))
        convert hc using 1; field_simp [h1t.ne', h1q.ne']
      convert hg.mul hf using 1; field_simp [h1t.ne']; ring
    have hd3 : HasDerivAt (fun u => 2 * (u - q) ^ 2) (4 * (t - q)) t := by
      have h := ((hasDerivAt_id t).sub_const q).pow 2 |>.const_mul 2
      convert h using 1; simp only [id]; ring
    simp only [φ, φ']
    convert (hd1.add hd2).sub hd3 using 1; ring
  have hφ'q : φ' q = 0 := by
    simp only [φ', div_self hq0.ne', div_self h1q.ne', Real.log_one, sub_self, mul_zero]
  have hφ'_d_all : ∀ t ∈ Set.Ioo 0 1, HasDerivAt φ' (t⁻¹ + (1 - t)⁻¹ - 4) t := by
    intro t ⟨ht0, ht1⟩
    have h1t : 0 < 1 - t := by linarith
    simp only [φ']
    have h1 : HasDerivAt (fun u => Real.log (u / q)) t⁻¹ t := by
      have hc := (Real.hasDerivAt_log (div_pos ht0 hq0).ne').comp t
                  ((hasDerivAt_id t).div_const q)
      convert hc using 1; field_simp [ht0.ne', hq0.ne']
    have h2 : HasDerivAt (fun u => Real.log ((1 - u) / (1 - q))) (-(1 - t)⁻¹) t := by
      have hg : HasDerivAt (fun u : ℝ => 1 - u) (-1) t := by
        have h := (hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)
        convert h using 1; norm_num
      have hc := (Real.hasDerivAt_log (div_pos h1t h1q).ne').comp t (hg.div_const (1 - q))
      convert hc using 1; field_simp [h1t.ne', h1q.ne']
    have h3 : HasDerivAt (fun u => 4 * (u - q)) (4 : ℝ) t := by
      convert ((hasDerivAt_id t).sub_const q).const_mul 4 using 1; ring
    convert (h1.sub h2).sub h3 using 1; ring
  have hφ'_mono : MonotoneOn φ' (Set.Ioo 0 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioo 0 1)
    · simp only [φ']
      apply ContinuousOn.sub (ContinuousOn.sub _ _) _
      · exact Real.continuousOn_log.comp (continuousOn_id.div_const q)
            (fun t ht => (div_pos ht.1 hq0).ne')
      · exact Real.continuousOn_log.comp
            ((continuousOn_const.sub continuousOn_id).div_const (1 - q))
            (fun t ht => (div_pos (by linarith [ht.2]) h1q).ne')
      · exact continuousOn_const.mul (continuousOn_id.sub continuousOn_const)
    · intro t ht; rw [interior_Ioo] at ht
      exact (hφ'_d_all t ht).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ioo] at ht
      have ht0 : 0 < t := ht.1; have ht1 : t < 1 := ht.2
      have h1t : 0 < 1 - t := by linarith
      rw [(hφ'_d_all t ht).deriv]
      have hprod_pos : 0 < t * (1 - t) := mul_pos ht0 h1t
      have hprod_le : t * (1 - t) ≤ 1 / 4 := by nlinarith [sq_nonneg (t - 1/2)]
      have heq : t⁻¹ + (1 - t)⁻¹ - 4 = (1 - 4 * (t * (1 - t))) / (t * (1 - t)) := by
        field_simp [ht0.ne', h1t.ne']; ring
      rw [heq]; apply div_nonneg _ hprod_pos.le; nlinarith
  have hq_in : q ∈ Set.Ioo 0 1 := ⟨hq0, hq1⟩
  by_cases hpq : q ≤ p
  · have hcont : ContinuousOn φ (Set.Icc q p) := by
      simp only [φ]
      apply ContinuousOn.sub (ContinuousOn.add _ _) _
      · apply ContinuousOn.mul continuousOn_id
        apply Real.continuousOn_log.comp (continuousOn_id.div_const q)
        intro t ht; exact (div_pos (lt_of_lt_of_le hq0 ht.1) hq0).ne'
      · apply ContinuousOn.mul (continuousOn_const.sub continuousOn_id)
        apply Real.continuousOn_log.comp
              ((continuousOn_const.sub continuousOn_id).div_const (1 - q))
        intro t ht
        simp only [Function.id_def]
        exact (div_pos (by linarith [ht.2]) h1q).ne'
      · exact continuousOn_const.mul ((continuousOn_id.sub continuousOn_const).pow 2)
    have hmono : MonotoneOn φ (Set.Icc q p) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc q p) hcont
      · intro t ht; rw [interior_Icc] at ht
        have ht_in : t ∈ Set.Ioo 0 1 :=
          ⟨by linarith [ht.1, hq0], by linarith [ht.2, hp1]⟩
        exact (hφ_deriv t ht_in).differentiableAt.differentiableWithinAt
      · intro t ht; rw [interior_Icc] at ht
        have ht_in : t ∈ Set.Ioo 0 1 :=
          ⟨by linarith [ht.1, hq0], by linarith [ht.2, hp1]⟩
        rw [(hφ_deriv t ht_in).deriv]
        have := hφ'_mono hq_in ht_in (le_of_lt ht.1)
        linarith [hφ'q ▸ this]
    have key := hmono (Set.left_mem_Icc.mpr hpq) (Set.right_mem_Icc.mpr hpq) hpq
    linarith [hφq ▸ key]
  · have hpq : p < q := not_le.mp hpq
    have hcont : ContinuousOn φ (Set.Icc p q) := by
      simp only [φ]
      apply ContinuousOn.sub (ContinuousOn.add _ _) _
      · apply ContinuousOn.mul continuousOn_id
        apply Real.continuousOn_log.comp (continuousOn_id.div_const q)
        intro t ht; exact (div_pos (lt_of_lt_of_le hp0 ht.1) hq0).ne'
      · apply ContinuousOn.mul (continuousOn_const.sub continuousOn_id)
        apply Real.continuousOn_log.comp
              ((continuousOn_const.sub continuousOn_id).div_const (1 - q))
        intro t ht
        simp only [Function.id_def]
        exact (div_pos (by linarith [ht.2]) h1q).ne'
      · exact continuousOn_const.mul ((continuousOn_id.sub continuousOn_const).pow 2)
    have hanti : AntitoneOn φ (Set.Icc p q) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc p q) hcont
      · intro t ht; rw [interior_Icc] at ht
        have ht_in : t ∈ Set.Ioo 0 1 :=
          ⟨by linarith [ht.1, hp0], by linarith [ht.2, hq1]⟩
        exact (hφ_deriv t ht_in).differentiableAt.differentiableWithinAt
      · intro t ht; rw [interior_Icc] at ht
        have ht_in : t ∈ Set.Ioo 0 1 :=
          ⟨by linarith [ht.1, hp0], by linarith [ht.2, hq1]⟩
        rw [(hφ_deriv t ht_in).deriv]
        have := hφ'_mono ht_in hq_in (le_of_lt ht.2)
        linarith [hφ'q ▸ this]
    have key := hanti (Set.left_mem_Icc.mpr hpq.le) (Set.right_mem_Icc.mpr hpq.le) hpq.le
    linarith [hφq ▸ key]

/-- KL(Bern(μ₀) ‖ Bern(μ₁)) ≤ 16Δ² where μ₀ = ½+Δ, μ₁ = ½−Δ, Δ ≤ ¼.
    Proof: KL = 2Δ · log(μ₀/μ₁); set t = 4Δ/(1−2Δ) and bound log(1+t) ≤ t. -/
theorem bernoulli_kl_upper_bound (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ4 : Δ ≤ 1 / 4) :
    let μ₀ := 1 / 2 + Δ
    let μ₁ := 1 / 2 - Δ
    klBern μ₀ μ₁ ≤ 16 * Δ ^ 2 := by
  set μ₀ := 1 / 2 + Δ
  set μ₁ := 1 / 2 - Δ
  have hμ₀  : 0 < μ₀     := by simp [μ₀]; linarith
  have hμ₁  : 0 < μ₁     := by simp [μ₁]; linarith
  have h1mΔ : 0 < 1 - 2 * Δ := by linarith
  have hswap₀ : 1 - μ₀ = μ₁ := by simp [μ₀, μ₁]; ring
  have hswap₁ : 1 - μ₁ = μ₀ := by simp [μ₀, μ₁]; ring
  have kl_eq : klBern μ₀ μ₁ = 2 * Δ * Real.log (μ₀ / μ₁) := by
    simp only [klBern, hswap₀, hswap₁]
    rw [show Real.log (μ₁ / μ₀) = -Real.log (μ₀ / μ₁) from by
      rw [Real.log_div hμ₁.ne' hμ₀.ne', Real.log_div hμ₀.ne' hμ₁.ne']; ring]
    have hd : μ₀ - μ₁ = 2 * Δ := by simp [μ₀, μ₁]; ring
    nlinarith [mul_comm μ₀ (Real.log (μ₀ / μ₁)), mul_comm μ₁ (Real.log (μ₀ / μ₁))]
  set t := 4 * Δ / (1 - 2 * Δ)
  have ratio_eq : μ₀ / μ₁ = 1 + t := by simp only [μ₀, μ₁, t]; field_simp; ring
  have ht_gt  : -1 < t := by have : 0 < t := div_pos (by linarith) h1mΔ; linarith
  have hlog   : Real.log (μ₀ / μ₁) ≤ t := ratio_eq ▸ log_one_add_le ht_gt
  have hbound : 8 * Δ ^ 2 / (1 - 2 * Δ) ≤ 16 * Δ ^ 2 := by
    rw [div_le_iff₀ h1mΔ]; nlinarith [sq_nonneg Δ]
  have ht_val : 2 * Δ * t = 8 * Δ ^ 2 / (1 - 2 * Δ) := by simp [t]; field_simp; ring
  linarith [mul_le_mul_of_nonneg_left hlog (by linarith : (0:ℝ) ≤ 2 * Δ)]

end BernoulliKL

-- §10  PINSKER'S INEQUALITY

section Pinsker

private lemma sum_kl_div_ge {α : Type*} {s : Finset α} {f g : α → ℝ}
    (hf  : ∀ x ∈ s, 0 ≤ f x)
    (hg  : ∀ x ∈ s, 0 < g x)
    (hfS : 0 < ∑ x ∈ s, f x)
    (hgS : 0 < ∑ x ∈ s, g x) :
    (∑ x ∈ s, f x) * Real.log ((∑ x ∈ s, f x) / (∑ x ∈ s, g x)) ≤
    ∑ x ∈ s, f x * Real.log (f x / g x) := by
  set c := (∑ x ∈ s, f x) / (∑ x ∈ s, g x) with hc_def
  have hc : 0 < c := div_pos hfS hgS
  have hpt : ∀ x ∈ s, f x + f x * Real.log c - c * g x ≤ f x * Real.log (f x / g x) := by
    intro x hxs
    by_cases hfx : f x = 0
    · simp only [hfx, zero_mul, zero_add, zero_sub, zero_div, Real.log_zero]
      linarith [mul_pos hc (hg x hxs)]
    · have hfx_pos : 0 < f x := lt_of_le_of_ne (hf x hxs) (Ne.symm hfx)
      have harg : 0 < c * g x / f x := div_pos (mul_pos hc (hg x hxs)) hfx_pos
      have hlog := log_le_sub_one harg
      rw [Real.log_div (mul_pos hc (hg x hxs)).ne' hfx_pos.ne',
          Real.log_mul hc.ne' (hg x hxs).ne'] at hlog
      have hmul : f x * Real.log c + f x * Real.log (g x) - f x * Real.log (f x) ≤
                  c * g x - f x :=
        calc f x * Real.log c + f x * Real.log (g x) - f x * Real.log (f x)
            = f x * (Real.log c + Real.log (g x) - Real.log (f x)) := by ring
          _ ≤ f x * (c * g x / f x - 1) := mul_le_mul_of_nonneg_left hlog hfx_pos.le
          _ = c * g x - f x := by field_simp [hfx_pos.ne']
      rw [Real.log_div hfx_pos.ne' (hg x hxs).ne']; linarith
  have hsum : ∑ x ∈ s, (f x + f x * Real.log c - c * g x) =
              (∑ x ∈ s, f x) * Real.log c := by
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
               ← Finset.mul_sum, ← Finset.sum_mul]
    linarith [show c * ∑ x ∈ s, g x = ∑ x ∈ s, f x from div_mul_cancel₀ _ hgS.ne']
  linarith [Finset.sum_le_sum hpt]

private lemma klBern_one_ge {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    Real.log (1 / q) ≥ 2 * (1 - q) ^ 2 := by
  rw [ge_iff_le, ← sub_nonneg]
  have hgoal : Real.log (1 / q) - 2 * (1 - q) ^ 2 =
               -Real.log q - 2 * (1 - q) ^ 2 := by
    rw [Real.log_div one_ne_zero hq0.ne', Real.log_one]; ring
  rw [hgoal]
  set ψ : ℝ → ℝ := fun t => -Real.log t - 2 * (1 - t) ^ 2 with hψ_def
  have hψ1 : ψ 1 = 0 := by simp [ψ, Real.log_one]
  have hderiv : ∀ t ∈ Set.Ioo q 1, HasDerivAt ψ (-t⁻¹ + 4 * (1 - t)) t := by
    intro t ⟨htq, _⟩
    have ht0 : 0 < t := lt_trans hq0 htq
    have hlog : HasDerivAt (fun u => -Real.log u) (-t⁻¹) t :=
      (Real.hasDerivAt_log ht0.ne').neg
    have hpoly : HasDerivAt (fun u => -2 * (1 - u) ^ 2) (4 * (1 - t)) t := by
      have h1 : HasDerivAt (fun u : ℝ => 1 - u) (-1 : ℝ) t := by
        have h := (hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)
        convert h using 1
        norm_num
      have h2 := (h1.pow 2).const_mul (-2 : ℝ)
      convert h2 using 1
      push_cast; ring
    convert hlog.add hpoly using 1
    funext s; simp [ψ]; ring
  have hψ_anti : AntitoneOn ψ (Set.Icc q 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc q 1)
    · exact (Real.continuousOn_log.mono
                (fun t ht => (lt_of_lt_of_le hq0 ht.1).ne')).neg.sub
              (((continuousOn_const.sub continuousOn_id).pow 2).const_mul 2)
    · intro t ht
      rw [interior_Icc] at ht
      exact (hderiv t ht).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have ht0 : 0 < t := lt_trans hq0 ht.1
      have hd : HasDerivAt ψ (-t⁻¹ + 4 * (1 - t)) t := hderiv t ht
      rw [hd.deriv,
          show -t⁻¹ + 4 * (1 - t) = (4 * t * (1 - t) - 1) / t from by
            field_simp [ht0.ne']; ring]
      exact div_nonpos_of_nonpos_of_nonneg
        (by nlinarith [sq_nonneg (2 * t - 1)]) ht0.le
  linarith [hψ1 ▸ hψ_anti (Set.left_mem_Icc.mpr hq1.le)
                            (Set.right_mem_Icc.mpr hq1.le) hq1.le]

private lemma klBern_ge_two_sq_ext (p q : ℝ)
    (hp0 : 0 < p) (hp1 : p ≤ 1) (hq0 : 0 < q) (hq1 : q < 1) :
    klBern p q ≥ 2 * (p - q) ^ 2 := by
  rcases hp1.eq_or_lt with rfl | hp1'
  · simp only [klBern, sub_self, zero_mul, add_zero, one_mul]
    exact klBern_one_ge hq0 hq1
  · exact bernoulli_kl_lower_bound p q hp0 hp1' hq0 hq1

theorem pinsker_inequality {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (P Q : PMF α)
    (h_ac : ∀ x, (P x).toReal = 0 ∨ 0 < (Q x).toReal) :
    tvDist P Q ≤ Real.sqrt (klDiv P Q / 2) := by
  by_cases hTV0 : tvDist P Q = 0
  · rw [hTV0]; exact Real.sqrt_nonneg _
  rw [← Real.sqrt_sq (tvDist_nonneg P Q)]
  apply Real.sqrt_le_sqrt
  have hTV_pos : 0 < tvDist P Q :=
    lt_of_le_of_ne (tvDist_nonneg P Q) (Ne.symm hTV0)
  haveI : DecidableEq α := Classical.decEq α
  let Apos : Finset α := Finset.univ.filter (fun x => (Q x).toReal ≤ (P x).toReal)
  let Aneg : Finset α := Finset.univ \ Apos
  set p := ∑ x ∈ Apos, (P x).toReal with hp_def
  set q := ∑ x ∈ Apos, (Q x).toReal with hq_def
  have hPsum : ∑ x : α, (P x).toReal = 1 := PMF_sum_toReal P
  have hQsum : ∑ x : α, (Q x).toReal = 1 := PMF_sum_toReal Q
  have hAnP : ∑ x ∈ Aneg, (P x).toReal = 1 - p := by
    have h := Finset.sum_sdiff (f := fun x => (P x).toReal) (Finset.subset_univ Apos)
    show ∑ x ∈ Finset.univ \ Apos, (P x).toReal = 1 - p; linarith [h, hPsum]
  have hAnQ : ∑ x ∈ Aneg, (Q x).toReal = 1 - q := by
    have h := Finset.sum_sdiff (f := fun x => (Q x).toReal) (Finset.subset_univ Apos)
    show ∑ x ∈ Finset.univ \ Apos, (Q x).toReal = 1 - q; linarith [h, hQsum]
  have habs_pos : ∑ x ∈ Apos, |(P x).toReal - (Q x).toReal| = p - q := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun x hx =>
      abs_of_nonneg (sub_nonneg.mpr (Finset.mem_filter.mp hx).2)
  have habs_neg : ∑ x ∈ Aneg, |(P x).toReal - (Q x).toReal| = p - q := by
    have hconv : ∑ x ∈ Aneg, |(P x).toReal - (Q x).toReal| =
                 ∑ x ∈ Aneg, ((Q x).toReal - (P x).toReal) :=
      Finset.sum_congr rfl fun x hx => by
        have hmem : x ∉ Apos := (Finset.mem_sdiff.mp hx).2
        have hlt : (P x).toReal < (Q x).toReal := by
          by_contra h
          push Not at h
          exact hmem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
        rw [abs_of_nonpos (sub_nonpos.mpr hlt.le)]; ring
    rw [hconv, Finset.sum_sub_distrib, hAnQ, hAnP]; ring
  have htv_eq : tvDist P Q = p - q := by
    simp only [tvDist]
    have h := Finset.sum_sdiff
                (f := fun x => |(P x).toReal - (Q x).toReal|)
                (Finset.subset_univ Apos)
    show (1 / 2) * ∑ x : α, |(P x).toReal - (Q x).toReal| = p - q
    have hsplit : ∑ x : α, |(P x).toReal - (Q x).toReal| =
        ∑ x ∈ Apos, |(P x).toReal - (Q x).toReal| +
        ∑ x ∈ Finset.univ \ Apos, |(P x).toReal - (Q x).toReal| := by
      linarith
    rw [hsplit, habs_pos, habs_neg]; ring
  have hp_pos : 0 < p := by
    have h0 : 0 ≤ p := by
      rw [hp_def]; exact Finset.sum_nonneg (fun x _ => ENNReal.toReal_nonneg)
    have hq0 : 0 ≤ q := by
      rw [hq_def]; exact Finset.sum_nonneg (fun x _ => ENNReal.toReal_nonneg)
    linarith [htv_eq ▸ hTV_pos]
  have hq_pos : 0 < q := by
    obtain ⟨x, hxA, hPx⟩ : ∃ x ∈ Apos, 0 < (P x).toReal := by
      by_contra h
      simp only [not_exists, not_and, not_lt] at h
      exact absurd hp_pos (not_lt.mpr (Finset.sum_nonpos h))
    exact lt_of_lt_of_le
      (by rcases h_ac x with hP | hQ
          · exact absurd (hP ▸ hPx) (lt_irrefl _)
          · exact hQ)
      (Finset.single_le_sum (fun x _ => ENNReal.toReal_nonneg) hxA)
  have hp_le1 : p ≤ 1 :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun _ _ _ => ENNReal.toReal_nonneg)).trans hPsum.le
  have hq_lt1 : q < 1 := by linarith [htv_eq ▸ hTV_pos]
  -- Restrict to the positive support of P within Apos
  let Apos_p : Finset α := Apos.filter (fun x => 0 < (P x).toReal)
  have hp_eq : ∑ x ∈ Apos_p, (P x).toReal = p := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro x hxApos hxnot
    simp only [Finset.mem_filter, not_and, not_lt] at hxnot
    exact le_antisymm (hxnot hxApos) ENNReal.toReal_nonneg
  have hq_eq : ∑ x ∈ Apos_p, (Q x).toReal = q := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro x hxApos hxnot
    simp only [Finset.mem_filter, not_and, not_lt] at hxnot
    have hPx : (P x).toReal = 0 :=
      le_antisymm (hxnot hxApos) ENNReal.toReal_nonneg
    exact le_antisymm ((Finset.mem_filter.mp hxApos).2.trans hPx.le) ENNReal.toReal_nonneg
  have hQApos_p : ∀ x ∈ Apos_p, 0 < (Q x).toReal := fun x hx => by
    rcases h_ac x with hP | hQ
    · exact absurd ((Finset.mem_filter.mp hx).2) (hP ▸ lt_irrefl _)
    · exact hQ
  have hQAneg : ∀ x ∈ Aneg, 0 < (Q x).toReal := fun x hx => by
    have hmem : x ∉ Apos := (Finset.mem_sdiff.mp hx).2
    have hlt : (P x).toReal < (Q x).toReal := by
      by_contra h
      push Not at h
      exact hmem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    linarith [show (0 : ℝ) ≤ (P x).toReal from ENNReal.toReal_nonneg]
  have hklPos : p * Real.log (p / q) ≤
      ∑ x ∈ Apos_p, (P x).toReal * Real.log ((P x).toReal / (Q x).toReal) := by
    have h := sum_kl_div_ge (fun x _ => ENNReal.toReal_nonneg) hQApos_p
                (hp_eq ▸ hp_pos) (hq_eq ▸ hq_pos)
    rwa [hp_eq, hq_eq] at h
  have hklNeg : (1 - p) * Real.log ((1 - p) / (1 - q)) ≤
      ∑ x ∈ Aneg, (P x).toReal * Real.log ((P x).toReal / (Q x).toReal) := by
    by_cases hp1 : p = 1
    · have hAnP0 : ∑ x ∈ Aneg, (P x).toReal = 0 := by
        have : p = 1 := hp1; linarith [hAnP]
      have hRHS : ∑ x ∈ Aneg, (P x).toReal * Real.log ((P x).toReal / (Q x).toReal) = 0 :=
        Finset.sum_eq_zero fun x hx => by
          have hPx : (P x).toReal = 0 := by
            apply le_antisymm _ ENNReal.toReal_nonneg
            have hle : (P x).toReal ≤ ∑ y ∈ Aneg, (P y).toReal :=
              calc (P x).toReal = ∑ y ∈ ({x} : Finset α), (P y).toReal := by simp
                _ ≤ ∑ y ∈ Aneg, (P y).toReal :=
                    Finset.sum_le_sum_of_subset_of_nonneg
                      (Finset.singleton_subset_iff.mpr hx)
                      (fun _ _ _ => ENNReal.toReal_nonneg)
            linarith [hAnP0]
          simp [hPx]
      simp [hp1, hRHS]
    · have hp_lt1 : p < 1 := lt_of_le_of_ne hp_le1 hp1
      have hAnP_pos : 0 < ∑ x ∈ Aneg, (P x).toReal := hAnP ▸ by linarith
      have hAnQ_pos : 0 < ∑ x ∈ Aneg, (Q x).toReal := by linarith [hAnQ]
      have h' := sum_kl_div_ge (fun x _ => ENNReal.toReal_nonneg) hQAneg
                   hAnP_pos hAnQ_pos
      rwa [hAnP, hAnQ] at h'
  have hklApos_eq :
      ∑ x ∈ Apos, (P x).toReal * Real.log ((P x).toReal / (Q x).toReal) =
      ∑ x ∈ Apos_p, (P x).toReal * Real.log ((P x).toReal / (Q x).toReal) := by
    symm; apply Finset.sum_subset (Finset.filter_subset _ _)
    intro x hxApos hxnot
    simp only [Finset.mem_filter, not_and, not_lt] at hxnot
    simp [le_antisymm (hxnot hxApos) ENNReal.toReal_nonneg]
  have hkl_ge_bern : klBern p q ≤ klDiv P Q := by
    have hkl_split : klDiv P Q =
        ∑ x ∈ Apos, (P x).toReal * Real.log ((P x).toReal / (Q x).toReal) +
        ∑ x ∈ Aneg, (P x).toReal * Real.log ((P x).toReal / (Q x).toReal) := by
      simp only [klDiv]
      have h := Finset.sum_sdiff
                  (f := fun x => (P x).toReal * Real.log ((P x).toReal / (Q x).toReal))
                  (Finset.subset_univ Apos)
      show ∑ x : α, (P x).toReal * Real.log ((P x).toReal / (Q x).toReal) =
           ∑ x ∈ Apos, (P x).toReal * Real.log ((P x).toReal / (Q x).toReal) +
           ∑ x ∈ Finset.univ \ Apos, (P x).toReal * Real.log ((P x).toReal / (Q x).toReal)
      linarith
    rw [hkl_split, hklApos_eq]; simp only [klBern]; linarith [hklPos, hklNeg]
  have hbern : 2 * (p - q) ^ 2 ≤ klBern p q :=
    klBern_ge_two_sq_ext p q hp_pos hp_le1 hq_pos hq_lt1
  nlinarith [sq_nonneg (p - q), htv_eq ▸ hTV_pos]

end Pinsker

end SixPrimitives.Phase1
