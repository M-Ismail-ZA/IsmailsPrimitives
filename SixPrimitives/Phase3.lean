import SixPrimitives.Phase0
import SixPrimitives.Phase1
import SixPrimitives.Phase2
import SixPrimitives.Phase2CMI
import Mathlib.Probability.Kernel.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Tactic
import Mathlib.Data.Finset.Basic

/-! # Ismail's Primitives — Phase 3: Necessity
Phase 3 proves that each of the six primitives is *necessary* for sublinear
regret in the Environment Class C -/

open MeasureTheory ProbabilityTheory Filter Real BigOperators Topology Set

-- PART A  AUXILIARY DEFINITIONS (namespace SixPrimitives.Phase3)

namespace SixPrimitives.Phase3

/-! # §0  TV-distance for Measures and Mutual-Information Sequence -/

section MIInfrastructure

variable {S A O Sig : Type*}
  [MeasurableSpace S] [MeasurableSpace A] [MeasurableSpace O]
  [MeasurableSpace Sig] [TopologicalSpace Sig] [BorelSpace Sig]

noncomputable def tvDistMeasure {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ ν : Measure α) : ℝ :=
  (1 / 2) * ∑ a : α, |(μ {a}).toReal - (ν {a}).toReal|

lemma tvDistMeasure_nonneg {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ ν : Measure α) :
    0 ≤ tvDistMeasure μ ν :=
  mul_nonneg (by norm_num) (Finset.sum_nonneg (fun _ _ => abs_nonneg _))

lemma tvDistMeasure_le_one {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    tvDistMeasure μ ν ≤ 1 := by
  simp only [tvDistMeasure]
  suffices h : ∑ a : α, |(μ {a}).toReal - (ν {a}).toReal| ≤ 2 by linarith
  calc ∑ a : α, |(μ {a}).toReal - (ν {a}).toReal|
      ≤ ∑ a : α, ((μ {a}).toReal + (ν {a}).toReal) :=
          Finset.sum_le_sum fun a _ => by
            have hμ := ENNReal.toReal_nonneg (a := μ {a})
            have hν := ENNReal.toReal_nonneg (a := ν {a})
            rw [abs_le]; constructor <;> linarith
    _ = ∑ a : α, (μ {a}).toReal + ∑ a : α, (ν {a}).toReal := Finset.sum_add_distrib
    _ ≤ 2 := by
        have hμ_sum : ∑ a : α, (μ {a}).toReal ≤ 1 := by
          have hfin : ∀ a ∈ (Finset.univ : Finset α), μ {a} ≠ ⊤ :=
            fun a _ => (measure_lt_top μ _).ne
          have huniv : ⋃ a ∈ (Finset.univ : Finset α), ({a} : Set α) = Set.univ := by
            ext x; simp
          have hsum : ∑ a ∈ (Finset.univ : Finset α), μ {a} = 1 := by
            rw [← measure_biUnion_finset
                  (fun x _ y _ hxy => Set.disjoint_singleton.mpr hxy)
                  (fun a _ => measurableSet_singleton a),
                huniv, measure_univ]
          have htoReal : ∑ a : α, (μ {a}).toReal = 1 := by
            rw [show ∑ a : α, (μ {a}).toReal =
                    ∑ a ∈ (Finset.univ : Finset α), (μ {a}).toReal by simp]
            rw [← ENNReal.toReal_sum hfin, hsum]
            simp
          linarith
        have hν_sum : ∑ a : α, (ν {a}).toReal ≤ 1 := by
          have hfin : ∀ a ∈ (Finset.univ : Finset α), ν {a} ≠ ⊤ :=
            fun a _ => (measure_lt_top ν _).ne
          have huniv : ⋃ a ∈ (Finset.univ : Finset α), ({a} : Set α) = Set.univ := by
            ext x; simp
          have hsum : ∑ a ∈ (Finset.univ : Finset α), ν {a} = 1 := by
            rw [← measure_biUnion_finset
                  (fun x _ y _ hxy => Set.disjoint_singleton.mpr hxy)
                  (fun a _ => measurableSet_singleton a),
                huniv, measure_univ]
          have htoReal : ∑ a : α, (ν {a}).toReal = 1 := by
            rw [show ∑ a : α, (ν {a}).toReal =
                    ∑ a ∈ (Finset.univ : Finset α), (ν {a}).toReal by simp]
            rw [← ENNReal.toReal_sum hfin, hsum]
            simp
          linarith
        linarith

noncomputable def miSeq [Fintype A] [MeasurableSingletonClass A]
    (env₀ env₁ : SixPrimitives.Env S A O)
    (alg : SixPrimitives.Algorithm A O Sig)
    (hEnv₀ : Phase2.EnvIsMarkov env₀)
    (hEnv₁ : Phase2.EnvIsMarkov env₁)
    (hAlg : Phase2.AlgIsMarkov alg)
    (t : ℕ) : ℝ :=
  tvDistMeasure
    (Phase2.actionMarginal env₀ alg env₀.hr_meas hEnv₀ hAlg (t + 1) ⟨t, Nat.lt_succ_self t⟩)
    (Phase2.actionMarginal env₁ alg env₁.hr_meas hEnv₁ hAlg (t + 1) ⟨t, Nat.lt_succ_self t⟩)

lemma miSeq_nonneg [Fintype A] [MeasurableSingletonClass A]
    (env₀ env₁ : SixPrimitives.Env S A O)
    (alg : SixPrimitives.Algorithm A O Sig)
    (hEnv₀ : Phase2.EnvIsMarkov env₀)
    (hEnv₁ : Phase2.EnvIsMarkov env₁)
    (hAlg : Phase2.AlgIsMarkov alg)
    (t : ℕ) :
    0 ≤ miSeq env₀ env₁ alg hEnv₀ hEnv₁ hAlg t :=
  tvDistMeasure_nonneg _ _

end MIInfrastructure
end SixPrimitives.Phase3

-- PART B  NECESSITY THEOREMS (namespace SixPrimitives)

namespace SixPrimitives

open SixPrimitives.Phase3

/-! # §1  Necessity of X₁ — Objective Tracking -/

section NecessityX1

theorem necessity_x1
    {Sig : Type*} [MeasurableSpace Sig] [TopologicalSpace Sig] [BorelSpace Sig]
    [MeasurableSingletonClass Sig] [MeasurableEq Sig]
    (bp : Phase2.BanditParam)
    (alg : SixPrimitives.Algorithm (Fin 2) Bool Sig)
    (hAlg : Phase2.AlgIsMarkov alg)
    (hLacks : LacksX₁ (miSeq
                (Phase2.env₁_0 bp) (Phase2.env₁_1 bp) alg
                (Phase2.env₁_0_isMarkov bp)
                (Phase2.env₁_1_isMarkov bp)
                hAlg)) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ T : ℕ in atTop,
      c * T ≤ regret (Phase2.env₁_0 bp) alg T + regret (Phase2.env₁_1 bp) alg T := by
  unfold LacksX₁ at hLacks
  rcases hLacks with ⟨B, hB_lt_half, h_limsup⟩
  have h_eta : ∃ η : ℝ, 0 < η ∧ B + η < 1/2 := by
    use (1/2 - B) / 2
    constructor <;> linarith
  rcases h_eta with ⟨η, hη_pos, hB_eta_lt_half⟩
  have h_limsup_lt : Filter.limsup (miSeq (Phase2.env₁_0 bp) (Phase2.env₁_1 bp) alg (Phase2.env₁_0_isMarkov bp) (Phase2.env₁_1_isMarkov bp) hAlg) Filter.atTop < B + η :=
    lt_of_le_of_lt h_limsup (by linarith)
  have hu : IsBoundedUnder (· ≤ ·) Filter.atTop (miSeq (Phase2.env₁_0 bp) (Phase2.env₁_1 bp) alg (Phase2.env₁_0_isMarkov bp) (Phase2.env₁_1_isMarkov bp) hAlg) := by
    use 1
    change ∀ᶠ t in Filter.atTop, miSeq (Phase2.env₁_0 bp) (Phase2.env₁_1 bp) alg (Phase2.env₁_0_isMarkov bp) (Phase2.env₁_1_isMarkov bp) hAlg t ≤ 1
    apply Filter.Eventually.of_forall
    intro t
    haveI inst1 : IsProbabilityMeasure (Phase2.actionMarginal (Phase2.env₁_0 bp) alg (Phase2.env₁_0 bp).hr_meas (Phase2.env₁_0_isMarkov bp) hAlg (t + 1) ⟨t, Nat.lt_succ_self t⟩) :=
      Phase2.actionMarginal_isProbability _ _ _ _ _ _ _
    haveI inst2 : IsProbabilityMeasure (Phase2.actionMarginal (Phase2.env₁_1 bp) alg (Phase2.env₁_1 bp).hr_meas (Phase2.env₁_1_isMarkov bp) hAlg (t + 1) ⟨t, Nat.lt_succ_self t⟩) :=
      Phase2.actionMarginal_isProbability _ _ _ _ _ _ _
    exact tvDistMeasure_le_one _ _
  have h_eventual_bound : ∀ᶠ t in Filter.atTop, miSeq (Phase2.env₁_0 bp) (Phase2.env₁_1 bp) alg (Phase2.env₁_0_isMarkov bp) (Phase2.env₁_1_isMarkov bp) hAlg t < B + η :=
    Filter.eventually_lt_of_limsup_lt h_limsup_lt hu
  have h_t0 : ∃ t₀ : ℕ, ∀ t ≥ t₀, miSeq (Phase2.env₁_0 bp) (Phase2.env₁_1 bp) alg (Phase2.env₁_0_isMarkov bp) (Phase2.env₁_1_isMarkov bp) hAlg t < B + η :=
    Filter.eventually_atTop.mp h_eventual_bound
  rcases h_t0 with ⟨t₀, ht₀⟩
  have h_opt_0 : ∀ T, SixPrimitives.optValue (Phase2.env₁_0 bp) T = (1 / 2 + bp.Δ) * T :=
    Phase2.env₁_optValue bp
  have h_opt_1 : ∀ T, SixPrimitives.optValue (Phase2.env₁_1 bp) T = (1/2 + bp.Δ) * T :=
    Phase2.env₁_1_optValue bp
  have h_regret_step_0 : ∀ T (t : Fin T),
      (1 / 2 + bp.Δ) - ∫ traj : Phase2.Trajectory (Fin 2) Bool T, (traj t).2.2 ∂ Phase2.trajMeasure (Phase2.env₁_0 bp) alg (Phase2.env₁_0 bp).hr_meas T =
      2 * bp.Δ * (Phase2.actionMarginal (Phase2.env₁_0 bp) alg (Phase2.env₁_0 bp).hr_meas (Phase2.env₁_0_isMarkov bp) hAlg T t {1}).toReal := by
    intro T t
    have h_ae_rew := Phase2.trajMeasure_step_reward_eq_unit
      (Phase2.env₁_0 bp) alg (Phase2.env₁_0 bp).hr_meas (Phase2.env₁_0_transDet bp)
      (Phase2.env₁_0_isMarkov bp) hAlg T t.val t.isLt
    have h_int_eq : ∫ traj : Phase2.Trajectory (Fin 2) Bool T, (traj t).2.2 ∂Phase2.trajMeasure (Phase2.env₁_0 bp) alg (Phase2.env₁_0 bp).hr_meas T =
        ∫ traj : Phase2.Trajectory (Fin 2) Bool T, (Phase2.env₁_0 bp).r ((), (traj t).1) ∂Phase2.trajMeasure (Phase2.env₁_0 bp) alg (Phase2.env₁_0 bp).hr_meas T :=
      integral_congr_ae h_ae_rew
    rw [h_int_eq]
    have h_r_expand : (fun (traj : Phase2.Trajectory (Fin 2) Bool T) => (Phase2.env₁_0 bp).r ((), (traj t).1)) =
        (fun traj => (1 / 2 + bp.Δ) * ({traj' : Phase2.Trajectory (Fin 2) Bool T | (traj' t).1 = 0}.indicator (fun _ => (1 : ℝ)) traj) +
                     (1 / 2 - bp.Δ) * ({traj' : Phase2.Trajectory (Fin 2) Bool T | (traj' t).1 = 1}.indicator (fun _ => (1 : ℝ)) traj)) := by
      ext traj
      dsimp [Phase2.env₁_0]
      by_cases h0 : (traj t).1 = 0
      · simp [h0]
      · have h1 : (traj t).1 = 1 := by omega
        simp [h1]
    rw [h_r_expand]
    have hs0_meas : MeasurableSet {traj' : Phase2.Trajectory (Fin 2) Bool T | (traj' t).1 = 0} :=
      (Phase2.measurable_traj_action t.val t.isLt) (measurableSet_singleton 0)
    have hs1_meas : MeasurableSet {traj' : Phase2.Trajectory (Fin 2) Bool T | (traj' t).1 = 1} :=
      (Phase2.measurable_traj_action t.val t.isLt) (measurableSet_singleton 1)
    haveI h_prob : IsProbabilityMeasure (Phase2.trajMeasure (Phase2.env₁_0 bp) alg (Phase2.env₁_0 bp).hr_meas T) :=
      Phase2.trajMeasure_isProbability (Phase2.env₁_0 bp) alg (Phase2.env₁_0 bp).hr_meas (Phase2.env₁_0_isMarkov bp) hAlg T
    have h_int_add : Integrable (fun traj : Phase2.Trajectory (Fin 2) Bool T => (1 / 2 + bp.Δ) * {traj' : Phase2.Trajectory (Fin 2) Bool T | (traj' t).1 = 0}.indicator (fun _ => (1 : ℝ)) traj) (Phase2.trajMeasure (Phase2.env₁_0 bp) alg (Phase2.env₁_0 bp).hr_meas T) :=
      ((integrable_const (1:ℝ)).indicator hs0_meas).const_mul (1 / 2 + bp.Δ)
    have h_int_add2 : Integrable (fun traj : Phase2.Trajectory (Fin 2) Bool T => (1 / 2 - bp.Δ) * {traj' : Phase2.Trajectory (Fin 2) Bool T | (traj' t).1 = 1}.indicator (fun _ => (1 : ℝ)) traj) (Phase2.trajMeasure (Phase2.env₁_0 bp) alg (Phase2.env₁_0 bp).hr_meas T) :=
      ((integrable_const (1:ℝ)).indicator hs1_meas).const_mul (1 / 2 - bp.Δ)
    rw [integral_add h_int_add h_int_add2]
    rw [integral_const_mul, integral_const_mul]
    have h_ind0 : ∫ traj, {traj' : Phase2.Trajectory (Fin 2) Bool T | (traj' t).1 = 0}.indicator (fun _ => (1 : ℝ)) traj ∂Phase2.trajMeasure (Phase2.env₁_0 bp) alg (Phase2.env₁_0 bp).hr_meas T = (Phase2.trajMeasure (Phase2.env₁_0 bp) alg (Phase2.env₁_0 bp).hr_meas T {traj' | (traj' t).1 = 0}).toReal := by
      rw [integral_indicator_const _ hs0_meas]
      simp only [smul_eq_mul, mul_one]
      rfl
    have h_ind1 : ∫ traj, {traj' : Phase2.Trajectory (Fin 2) Bool T | (traj' t).1 = 1}.indicator (fun _ => (1 : ℝ)) traj ∂Phase2.trajMeasure (Phase2.env₁_0 bp) alg (Phase2.env₁_0 bp).hr_meas T = (Phase2.trajMeasure (Phase2.env₁_0 bp) alg (Phase2.env₁_0 bp).hr_meas T {traj' | (traj' t).1 = 1}).toReal := by
      rw [integral_indicator_const _ hs1_meas]
      simp only [smul_eq_mul, mul_one]
      rfl
    rw [h_ind0, h_ind1]
    have h_marg0 : (Phase2.trajMeasure (Phase2.env₁_0 bp) alg (Phase2.env₁_0 bp).hr_meas T {traj' | (traj' t).1 = 0}).toReal = (Phase2.actionMarginal (Phase2.env₁_0 bp) alg (Phase2.env₁_0 bp).hr_meas (Phase2.env₁_0_isMarkov bp) hAlg T t {0}).toReal := by
      dsimp [Phase2.actionMarginal]
      have h_meas : Measurable (fun (traj : Phase2.Trajectory (Fin 2) Bool T) => (traj t).1) := Phase2.measurable_traj_action t.val t.isLt
      have h_map := Measure.map_apply h_meas (measurableSet_singleton 0) (μ := Phase2.trajMeasure (Phase2.env₁_0 bp) alg (Phase2.env₁_0 bp).hr_meas T)
      have h_set_eq : (fun (traj : Phase2.Trajectory (Fin 2) Bool T) => (traj t).1) ⁻¹' {0} = {traj' | (traj' t).1 = 0} := rfl
      rw [h_set_eq] at h_map
      congr 1
      exact h_map.symm
    have h_marg1 : (Phase2.trajMeasure (Phase2.env₁_0 bp) alg (Phase2.env₁_0 bp).hr_meas T {traj' | (traj' t).1 = 1}).toReal = (Phase2.actionMarginal (Phase2.env₁_0 bp) alg (Phase2.env₁_0 bp).hr_meas (Phase2.env₁_0_isMarkov bp) hAlg T t {1}).toReal := by
      dsimp [Phase2.actionMarginal]
      have h_meas : Measurable (fun (traj : Phase2.Trajectory (Fin 2) Bool T) => (traj t).1) := Phase2.measurable_traj_action t.val t.isLt
      have h_map := Measure.map_apply h_meas (measurableSet_singleton 1) (μ := Phase2.trajMeasure (Phase2.env₁_0 bp) alg (Phase2.env₁_0 bp).hr_meas T)
      have h_set_eq : (fun (traj : Phase2.Trajectory (Fin 2) Bool T) => (traj t).1) ⁻¹' {1} = {traj' | (traj' t).1 = 1} := rfl
      rw [h_set_eq] at h_map
      congr 1
      exact h_map.symm
    rw [h_marg0, h_marg1]
    haveI hμ_prob : IsProbabilityMeasure (Phase2.actionMarginal (Phase2.env₁_0 bp) alg (Phase2.env₁_0 bp).hr_meas (Phase2.env₁_0_isMarkov bp) hAlg T t) := Phase2.actionMarginal_isProbability _ _ _ _ _ _ _
    have h_sum_μ : ((Phase2.actionMarginal (Phase2.env₁_0 bp) alg (Phase2.env₁_0 bp).hr_meas (Phase2.env₁_0_isMarkov bp) hAlg T t) {0}).toReal + ((Phase2.actionMarginal (Phase2.env₁_0 bp) alg (Phase2.env₁_0 bp).hr_meas (Phase2.env₁_0_isMarkov bp) hAlg T t) {1}).toReal = 1 := by
      have h_disj : Disjoint ({0} : Set (Fin 2)) ({1} : Set (Fin 2)) := Set.disjoint_singleton.mpr (by decide)
      have h_union : ({0} : Set (Fin 2)) ∪ {1} = Set.univ := by ext x; simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_univ]; fin_cases x <;> decide
      have h_meas_eq : (Phase2.actionMarginal (Phase2.env₁_0 bp) alg (Phase2.env₁_0 bp).hr_meas (Phase2.env₁_0_isMarkov bp) hAlg T t) ({0} ∪ {1}) = (Phase2.actionMarginal (Phase2.env₁_0 bp) alg (Phase2.env₁_0 bp).hr_meas (Phase2.env₁_0_isMarkov bp) hAlg T t) {0} + (Phase2.actionMarginal (Phase2.env₁_0 bp) alg (Phase2.env₁_0 bp).hr_meas (Phase2.env₁_0_isMarkov bp) hAlg T t) {1} := measure_union h_disj (measurableSet_singleton 1)
      rw [h_union, measure_univ] at h_meas_eq
      have h_toReal : ((Phase2.actionMarginal (Phase2.env₁_0 bp) alg (Phase2.env₁_0 bp).hr_meas (Phase2.env₁_0_isMarkov bp) hAlg T t) {0} + (Phase2.actionMarginal (Phase2.env₁_0 bp) alg (Phase2.env₁_0 bp).hr_meas (Phase2.env₁_0_isMarkov bp) hAlg T t) {1}).toReal = (1 : ENNReal).toReal := by rw [← h_meas_eq]
      rw [ENNReal.toReal_one, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at h_toReal
      exact h_toReal
    have h_p0 : ((Phase2.actionMarginal (Phase2.env₁_0 bp) alg (Phase2.env₁_0 bp).hr_meas (Phase2.env₁_0_isMarkov bp) hAlg T t) {0}).toReal = 1 - ((Phase2.actionMarginal (Phase2.env₁_0 bp) alg (Phase2.env₁_0 bp).hr_meas (Phase2.env₁_0_isMarkov bp) hAlg T t) {1}).toReal := by linarith
    rw [h_p0]
    ring
  have h_regret_step_1 : ∀ T (t : Fin T),
      (1 / 2 + bp.Δ) - ∫ traj : Phase2.Trajectory (Fin 2) Bool T, (traj t).2.2 ∂ Phase2.trajMeasure (Phase2.env₁_1 bp) alg (Phase2.env₁_1 bp).hr_meas T =
      2 * bp.Δ * (Phase2.actionMarginal (Phase2.env₁_1 bp) alg (Phase2.env₁_1 bp).hr_meas (Phase2.env₁_1_isMarkov bp) hAlg T t {0}).toReal := by
    intro T t
    have h_ae_rew := Phase2.trajMeasure_step_reward_eq_unit
      (Phase2.env₁_1 bp) alg (Phase2.env₁_1 bp).hr_meas (Phase2.env₁_1_transDet bp)
      (Phase2.env₁_1_isMarkov bp) hAlg T t.val t.isLt
    have h_int_eq : ∫ traj : Phase2.Trajectory (Fin 2) Bool T, (traj t).2.2 ∂Phase2.trajMeasure (Phase2.env₁_1 bp) alg (Phase2.env₁_1 bp).hr_meas T =
        ∫ traj : Phase2.Trajectory (Fin 2) Bool T, (Phase2.env₁_1 bp).r ((), (traj t).1) ∂Phase2.trajMeasure (Phase2.env₁_1 bp) alg (Phase2.env₁_1 bp).hr_meas T :=
      integral_congr_ae h_ae_rew
    rw [h_int_eq]
    have h_r_expand : (fun (traj : Phase2.Trajectory (Fin 2) Bool T) => (Phase2.env₁_1 bp).r ((), (traj t).1)) =
        (fun traj => (1 / 2 - bp.Δ) * ({traj' : Phase2.Trajectory (Fin 2) Bool T | (traj' t).1 = 0}.indicator (fun _ => (1 : ℝ)) traj) +
                     (1 / 2 + bp.Δ) * ({traj' : Phase2.Trajectory (Fin 2) Bool T | (traj' t).1 = 1}.indicator (fun _ => (1 : ℝ)) traj)) := by
      ext traj
      dsimp [Phase2.env₁_1]
      by_cases h0 : (traj t).1 = 0
      · simp [h0]
      · have h1 : (traj t).1 = 1 := by omega
        simp [h1]
    rw [h_r_expand]
    have hs0_meas : MeasurableSet {traj' : Phase2.Trajectory (Fin 2) Bool T | (traj' t).1 = 0} :=
      (Phase2.measurable_traj_action t.val t.isLt) (measurableSet_singleton 0)
    have hs1_meas : MeasurableSet {traj' : Phase2.Trajectory (Fin 2) Bool T | (traj' t).1 = 1} :=
      (Phase2.measurable_traj_action t.val t.isLt) (measurableSet_singleton 1)
    haveI h_prob : IsProbabilityMeasure (Phase2.trajMeasure (Phase2.env₁_1 bp) alg (Phase2.env₁_1 bp).hr_meas T) :=
      Phase2.trajMeasure_isProbability (Phase2.env₁_1 bp) alg (Phase2.env₁_1 bp).hr_meas (Phase2.env₁_1_isMarkov bp) hAlg T
    have h_int_add : Integrable (fun traj : Phase2.Trajectory (Fin 2) Bool T => (1 / 2 - bp.Δ) * {traj' : Phase2.Trajectory (Fin 2) Bool T | (traj' t).1 = 0}.indicator (fun _ => (1 : ℝ)) traj) (Phase2.trajMeasure (Phase2.env₁_1 bp) alg (Phase2.env₁_1 bp).hr_meas T) :=
      ((integrable_const (1:ℝ)).indicator hs0_meas).const_mul (1 / 2 - bp.Δ)
    have h_int_add2 : Integrable (fun traj : Phase2.Trajectory (Fin 2) Bool T => (1 / 2 + bp.Δ) * {traj' : Phase2.Trajectory (Fin 2) Bool T | (traj' t).1 = 1}.indicator (fun _ => (1 : ℝ)) traj) (Phase2.trajMeasure (Phase2.env₁_1 bp) alg (Phase2.env₁_1 bp).hr_meas T) :=
      ((integrable_const (1:ℝ)).indicator hs1_meas).const_mul (1 / 2 + bp.Δ)
    rw [integral_add h_int_add h_int_add2]
    rw [integral_const_mul, integral_const_mul]
    have h_ind0 : ∫ traj, {traj' : Phase2.Trajectory (Fin 2) Bool T | (traj' t).1 = 0}.indicator (fun _ => (1 : ℝ)) traj ∂Phase2.trajMeasure (Phase2.env₁_1 bp) alg (Phase2.env₁_1 bp).hr_meas T = (Phase2.trajMeasure (Phase2.env₁_1 bp) alg (Phase2.env₁_1 bp).hr_meas T {traj' | (traj' t).1 = 0}).toReal := by
      rw [integral_indicator_const _ hs0_meas]
      simp only [smul_eq_mul, mul_one]
      rfl
    have h_ind1 : ∫ traj, {traj' : Phase2.Trajectory (Fin 2) Bool T | (traj' t).1 = 1}.indicator (fun _ => (1 : ℝ)) traj ∂Phase2.trajMeasure (Phase2.env₁_1 bp) alg (Phase2.env₁_1 bp).hr_meas T = (Phase2.trajMeasure (Phase2.env₁_1 bp) alg (Phase2.env₁_1 bp).hr_meas T {traj' | (traj' t).1 = 1}).toReal := by
      rw [integral_indicator_const _ hs1_meas]
      simp only [smul_eq_mul, mul_one]
      rfl
    rw [h_ind0, h_ind1]
    have h_marg0 : (Phase2.trajMeasure (Phase2.env₁_1 bp) alg (Phase2.env₁_1 bp).hr_meas T {traj' | (traj' t).1 = 0}).toReal = (Phase2.actionMarginal (Phase2.env₁_1 bp) alg (Phase2.env₁_1 bp).hr_meas (Phase2.env₁_1_isMarkov bp) hAlg T t {0}).toReal := by
      dsimp [Phase2.actionMarginal]
      have h_meas : Measurable (fun (traj : Phase2.Trajectory (Fin 2) Bool T) => (traj t).1) := Phase2.measurable_traj_action t.val t.isLt
      have h_map := Measure.map_apply h_meas (measurableSet_singleton 0) (μ := Phase2.trajMeasure (Phase2.env₁_1 bp) alg (Phase2.env₁_1 bp).hr_meas T)
      have h_set_eq : (fun (traj : Phase2.Trajectory (Fin 2) Bool T) => (traj t).1) ⁻¹' {0} = {traj' | (traj' t).1 = 0} := rfl
      rw [h_set_eq] at h_map
      congr 1
      exact h_map.symm
    have h_marg1 : (Phase2.trajMeasure (Phase2.env₁_1 bp) alg (Phase2.env₁_1 bp).hr_meas T {traj' | (traj' t).1 = 1}).toReal = (Phase2.actionMarginal (Phase2.env₁_1 bp) alg (Phase2.env₁_1 bp).hr_meas (Phase2.env₁_1_isMarkov bp) hAlg T t {1}).toReal := by
      dsimp [Phase2.actionMarginal]
      have h_meas : Measurable (fun (traj : Phase2.Trajectory (Fin 2) Bool T) => (traj t).1) := Phase2.measurable_traj_action t.val t.isLt
      have h_map := Measure.map_apply h_meas (measurableSet_singleton 1) (μ := Phase2.trajMeasure (Phase2.env₁_1 bp) alg (Phase2.env₁_1 bp).hr_meas T)
      have h_set_eq : (fun (traj : Phase2.Trajectory (Fin 2) Bool T) => (traj t).1) ⁻¹' {1} = {traj' | (traj' t).1 = 1} := rfl
      rw [h_set_eq] at h_map
      congr 1
      exact h_map.symm
    rw [h_marg0, h_marg1]
    haveI hμ_prob : IsProbabilityMeasure (Phase2.actionMarginal (Phase2.env₁_1 bp) alg (Phase2.env₁_1 bp).hr_meas (Phase2.env₁_1_isMarkov bp) hAlg T t) := Phase2.actionMarginal_isProbability _ _ _ _ _ _ _
    have h_sum_μ : ((Phase2.actionMarginal (Phase2.env₁_1 bp) alg (Phase2.env₁_1 bp).hr_meas (Phase2.env₁_1_isMarkov bp) hAlg T t) {0}).toReal + ((Phase2.actionMarginal (Phase2.env₁_1 bp) alg (Phase2.env₁_1 bp).hr_meas (Phase2.env₁_1_isMarkov bp) hAlg T t) {1}).toReal = 1 := by
      have h_disj : Disjoint ({0} : Set (Fin 2)) ({1} : Set (Fin 2)) := Set.disjoint_singleton.mpr (by decide)
      have h_union : ({0} : Set (Fin 2)) ∪ {1} = Set.univ := by ext x; simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_univ]; fin_cases x <;> decide
      have h_meas_eq : (Phase2.actionMarginal (Phase2.env₁_1 bp) alg (Phase2.env₁_1 bp).hr_meas (Phase2.env₁_1_isMarkov bp) hAlg T t) ({0} ∪ {1}) = (Phase2.actionMarginal (Phase2.env₁_1 bp) alg (Phase2.env₁_1 bp).hr_meas (Phase2.env₁_1_isMarkov bp) hAlg T t) {0} + (Phase2.actionMarginal (Phase2.env₁_1 bp) alg (Phase2.env₁_1 bp).hr_meas (Phase2.env₁_1_isMarkov bp) hAlg T t) {1} := measure_union h_disj (measurableSet_singleton 1)
      rw [h_union, measure_univ] at h_meas_eq
      have h_toReal : ((Phase2.actionMarginal (Phase2.env₁_1 bp) alg (Phase2.env₁_1 bp).hr_meas (Phase2.env₁_1_isMarkov bp) hAlg T t) {0} + (Phase2.actionMarginal (Phase2.env₁_1 bp) alg (Phase2.env₁_1 bp).hr_meas (Phase2.env₁_1_isMarkov bp) hAlg T t) {1}).toReal = (1 : ENNReal).toReal := by rw [← h_meas_eq]
      rw [ENNReal.toReal_one, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at h_toReal
      exact h_toReal
    have h_p1 : ((Phase2.actionMarginal (Phase2.env₁_1 bp) alg (Phase2.env₁_1 bp).hr_meas (Phase2.env₁_1_isMarkov bp) hAlg T t) {1}).toReal = 1 - ((Phase2.actionMarginal (Phase2.env₁_1 bp) alg (Phase2.env₁_1 bp).hr_meas (Phase2.env₁_1_isMarkov bp) hAlg T t) {0}).toReal := by linarith
    rw [h_p1]
    ring
  have h_marginal_consist_0 : ∀ T (t : Fin T),
      (Phase2.actionMarginal (Phase2.env₁_0 bp) alg (Phase2.env₁_0 bp).hr_meas (Phase2.env₁_0_isMarkov bp) hAlg T t {1}).toReal =
      (Phase2.actionMarginal (Phase2.env₁_0 bp) alg (Phase2.env₁_0 bp).hr_meas (Phase2.env₁_0_isMarkov bp) hAlg (t.val + 1) ⟨t.val, Nat.lt_succ_self _⟩ {1}).toReal := by
    intro T t
    dsimp [Phase2.actionMarginal]
    have ht_le : t.val + 1 ≤ T := t.isLt
    have h_meas_t : Measurable (fun (traj : Phase2.Trajectory (Fin 2) Bool T) => (traj t).1) := Phase2.measurable_traj_action t.val t.isLt
    have h_meas_t1 : Measurable (fun (traj' : Phase2.Trajectory (Fin 2) Bool (t.val + 1)) => (traj' ⟨t.val, Nat.lt_succ_self _⟩).1) := Phase2.measurable_traj_action t.val (Nat.lt_succ_self _)
    have h_meas_set : MeasurableSet ((fun (traj' : Phase2.Trajectory (Fin 2) Bool (t.val + 1)) => (traj' ⟨t.val, Nat.lt_succ_self _⟩).1) ⁻¹' {1}) :=
      h_meas_t1 (measurableSet_singleton 1)
    have h_trunc := Phase2.trajMeasure_truncation (Phase2.env₁_0 bp) alg (Phase2.env₁_0 bp).hr_meas (Phase2.env₁_0_isMarkov bp) hAlg T (t.val + 1) ht_le _ h_meas_set
    congr 1
    rw [Measure.map_apply h_meas_t (measurableSet_singleton 1)]
    rw [Measure.map_apply h_meas_t1 (measurableSet_singleton 1)]
    have h_set_eq : (fun (traj : Phase2.Trajectory (Fin 2) Bool T) => (traj t).1) ⁻¹' {1} =
        {traj : Phase2.Trajectory (Fin 2) Bool T | (fun (i : Fin (t.val + 1)) => traj (Fin.castLE ht_le i)) ∈ (fun (traj' : Phase2.Trajectory (Fin 2) Bool (t.val + 1)) => (traj' ⟨t.val, Nat.lt_succ_self _⟩).1) ⁻¹' {1}} := by
      ext traj
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
      rfl
    rw [h_set_eq]
    exact h_trunc
  have h_marginal_consist_1 : ∀ T (t : Fin T),
      (Phase2.actionMarginal (Phase2.env₁_1 bp) alg (Phase2.env₁_1 bp).hr_meas (Phase2.env₁_1_isMarkov bp) hAlg T t {0}).toReal =
      (Phase2.actionMarginal (Phase2.env₁_1 bp) alg (Phase2.env₁_1 bp).hr_meas (Phase2.env₁_1_isMarkov bp) hAlg (t.val + 1) ⟨t.val, Nat.lt_succ_self _⟩ {0}).toReal := by
    intro T t
    dsimp [Phase2.actionMarginal]
    have ht_le : t.val + 1 ≤ T := t.isLt
    have h_meas_t : Measurable (fun (traj : Phase2.Trajectory (Fin 2) Bool T) => (traj t).1) := Phase2.measurable_traj_action t.val t.isLt
    have h_meas_t1 : Measurable (fun (traj' : Phase2.Trajectory (Fin 2) Bool (t.val + 1)) => (traj' ⟨t.val, Nat.lt_succ_self _⟩).1) := Phase2.measurable_traj_action t.val (Nat.lt_succ_self _)
    have h_meas_set : MeasurableSet ((fun (traj' : Phase2.Trajectory (Fin 2) Bool (t.val + 1)) => (traj' ⟨t.val, Nat.lt_succ_self _⟩).1) ⁻¹' {0}) :=
      h_meas_t1 (measurableSet_singleton 0)
    have h_trunc := Phase2.trajMeasure_truncation (Phase2.env₁_1 bp) alg (Phase2.env₁_1 bp).hr_meas (Phase2.env₁_1_isMarkov bp) hAlg T (t.val + 1) ht_le _ h_meas_set
    congr 1
    rw [Measure.map_apply h_meas_t (measurableSet_singleton 0)]
    rw [Measure.map_apply h_meas_t1 (measurableSet_singleton 0)]
    have h_set_eq : (fun (traj : Phase2.Trajectory (Fin 2) Bool T) => (traj t).1) ⁻¹' {0} =
        {traj : Phase2.Trajectory (Fin 2) Bool T | (fun (i : Fin (t.val + 1)) => traj (Fin.castLE ht_le i)) ∈ (fun (traj' : Phase2.Trajectory (Fin 2) Bool (t.val + 1)) => (traj' ⟨t.val, Nat.lt_succ_self _⟩).1) ⁻¹' {0}} := by
      ext traj
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
      rfl
    rw [h_set_eq]
    exact h_trunc
  have h_le_cam : ∀ t,
      1 - miSeq (Phase2.env₁_0 bp) (Phase2.env₁_1 bp) alg (Phase2.env₁_0_isMarkov bp) (Phase2.env₁_1_isMarkov bp) hAlg t ≤
      (Phase2.actionMarginal (Phase2.env₁_0 bp) alg (Phase2.env₁_0 bp).hr_meas (Phase2.env₁_0_isMarkov bp) hAlg (t + 1) ⟨t, Nat.lt_succ_self t⟩ {1}).toReal +
      (Phase2.actionMarginal (Phase2.env₁_1 bp) alg (Phase2.env₁_1 bp).hr_meas (Phase2.env₁_1_isMarkov bp) hAlg (t + 1) ⟨t, Nat.lt_succ_self t⟩ {0}).toReal := by
    intro t
    dsimp [miSeq, tvDistMeasure]
    set μ := Phase2.actionMarginal (Phase2.env₁_0 bp) alg (Phase2.env₁_0 bp).hr_meas (Phase2.env₁_0_isMarkov bp) hAlg (t + 1) ⟨t, Nat.lt_succ_self t⟩
    set ν := Phase2.actionMarginal (Phase2.env₁_1 bp) alg (Phase2.env₁_1 bp).hr_meas (Phase2.env₁_1_isMarkov bp) hAlg (t + 1) ⟨t, Nat.lt_succ_self t⟩
    haveI hμ_prob : IsProbabilityMeasure μ := Phase2.actionMarginal_isProbability _ _ _ _ _ _ _
    haveI hν_prob : IsProbabilityMeasure ν := Phase2.actionMarginal_isProbability _ _ _ _ _ _ _
    have h_sum_μ : (μ {0}).toReal + (μ {1}).toReal = 1 := by
      have h_disj : Disjoint ({0} : Set (Fin 2)) ({1} : Set (Fin 2)) := Set.disjoint_singleton.mpr (by decide)
      have h_union : ({0} : Set (Fin 2)) ∪ {1} = Set.univ := by ext x; simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_univ]; fin_cases x <;> decide
      have h_meas_eq : μ ({0} ∪ {1}) = μ {0} + μ {1} := measure_union h_disj (measurableSet_singleton 1)
      rw [h_union, measure_univ] at h_meas_eq
      have h_toReal : (μ {0} + μ {1}).toReal = (1 : ENNReal).toReal := by rw [← h_meas_eq]
      rw [ENNReal.toReal_one, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at h_toReal
      exact h_toReal
    have h_sum_ν : (ν {0}).toReal + (ν {1}).toReal = 1 := by
      have h_disj : Disjoint ({0} : Set (Fin 2)) ({1} : Set (Fin 2)) := Set.disjoint_singleton.mpr (by decide)
      have h_union : ({0} : Set (Fin 2)) ∪ {1} = Set.univ := by ext x; simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_univ]; fin_cases x <;> decide
      have h_meas_eq : ν ({0} ∪ {1}) = ν {0} + ν {1} := measure_union h_disj (measurableSet_singleton 1)
      rw [h_union, measure_univ] at h_meas_eq
      have h_toReal : (ν {0} + ν {1}).toReal = (1 : ENNReal).toReal := by rw [← h_meas_eq]
      rw [ENNReal.toReal_one, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at h_toReal
      exact h_toReal
    have h_sum_tv : ∑ a : Fin 2, |(μ {a}).toReal - (ν {a}).toReal| = |(μ {0}).toReal - (ν {0}).toReal| + |(μ {1}).toReal - (ν {1}).toReal| := by
      exact Fin.sum_univ_two (fun a => |(μ {a}).toReal - (ν {a}).toReal|)
    rw [h_sum_tv]
    have hp1 : (μ {1}).toReal = 1 - (μ {0}).toReal := by linarith
    have hq1 : (ν {1}).toReal = 1 - (ν {0}).toReal := by linarith
    rw [hp1, hq1]
    have h_abs : |1 - (μ {0}).toReal - (1 - (ν {0}).toReal)| = |(μ {0}).toReal - (ν {0}).toReal| := by
      have h_eq : 1 - (μ {0}).toReal - (1 - (ν {0}).toReal) = (ν {0}).toReal - (μ {0}).toReal := by ring
      rw [h_eq, abs_sub_comm]
    rw [h_abs, ← two_mul, ← mul_assoc, div_mul_cancel₀ 1 (by norm_num), one_mul]
    have h_abs_le : -|(μ {0}).toReal - (ν {0}).toReal| ≤ (ν {0}).toReal - (μ {0}).toReal := by
      rw [abs_sub_comm]
      exact neg_abs_le ((ν {0}).toReal - (μ {0}).toReal)
    linarith
  have h_sum_regret : ∀ T ≥ t₀,
      2 * bp.Δ * (1 - (B + η)) * ((T - t₀ : ℕ) : ℝ) ≤
      regret (Phase2.env₁_0 bp) alg T + regret (Phase2.env₁_1 bp) alg T := by
    intro T hT
    have h_bound0 : ∀ (s : Unit) (a : Fin 2), |(Phase2.env₁_0 bp).r (s, a)| ≤ 1 / 2 + bp.Δ := by
      intro s a; dsimp [Phase2.env₁_0];
      split_ifs
      · rw [abs_of_pos (by linarith [bp.hΔ0])]
      · rw [abs_of_pos (by linarith [bp.hΔ1])]; linarith [bp.hΔ0]
    have h_bound1 : ∀ (s : Unit) (a : Fin 2), |(Phase2.env₁_1 bp).r (s, a)| ≤ 1 / 2 + bp.Δ := by
      intro s a; dsimp [Phase2.env₁_1];
      split_ifs
      · rw [abs_of_pos (by linarith [bp.hΔ1])]; linarith [bp.hΔ0]
      · rw [abs_of_pos (by linarith [bp.hΔ0])]
    have h_T_mul : (1 / 2 + bp.Δ) * (T : ℝ) = ∑ _t : Fin T, (1 / 2 + bp.Δ) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    have h_regret_eq : regret (Phase2.env₁_0 bp) alg T + regret (Phase2.env₁_1 bp) alg T =
      ((∑ _t : Fin T, (1 / 2 + bp.Δ)) - ∑ t : Fin T, ∫ (traj : Phase2.Trajectory (Fin 2) Bool T), (traj t).2.2 ∂Phase2.trajMeasure (Phase2.env₁_0 bp) alg (Phase2.env₁_0 bp).hr_meas T) +
      ((∑ _t : Fin T, (1 / 2 + bp.Δ)) - ∑ t : Fin T, ∫ (traj : Phase2.Trajectory (Fin 2) Bool T), (traj t).2.2 ∂Phase2.trajMeasure (Phase2.env₁_1 bp) alg (Phase2.env₁_1 bp).hr_meas T) := by
      unfold regret
      rw [h_opt_0 T, h_opt_1 T]
      rw [Phase2.algValue_eq_algValue', Phase2.algValue_eq_algValue']
      rw [Phase2.algValue'_eq_sum (Phase2.env₁_0 bp) alg (Phase2.env₁_0 bp).hr_meas (Phase2.env₁_0_isMarkov bp) hAlg h_bound0 T]
      rw [Phase2.algValue'_eq_sum (Phase2.env₁_1 bp) alg (Phase2.env₁_1 bp).hr_meas (Phase2.env₁_1_isMarkov bp) hAlg h_bound1 T]
      rw [h_T_mul]
    have h_sum_combine : ((∑ _t : Fin T, (1 / 2 + bp.Δ)) - ∑ t : Fin T, ∫ (traj : Phase2.Trajectory (Fin 2) Bool T), (traj t).2.2 ∂Phase2.trajMeasure (Phase2.env₁_0 bp) alg (Phase2.env₁_0 bp).hr_meas T) + ((∑ _t : Fin T, (1 / 2 + bp.Δ)) - ∑ t : Fin T, ∫ (traj : Phase2.Trajectory (Fin 2) Bool T), (traj t).2.2 ∂Phase2.trajMeasure (Phase2.env₁_1 bp) alg (Phase2.env₁_1 bp).hr_meas T) =
                        ∑ t : Fin T, (((1 / 2 + bp.Δ) - ∫ (traj : Phase2.Trajectory (Fin 2) Bool T), (traj t).2.2 ∂Phase2.trajMeasure (Phase2.env₁_0 bp) alg (Phase2.env₁_0 bp).hr_meas T) + ((1 / 2 + bp.Δ) - ∫ (traj : Phase2.Trajectory (Fin 2) Bool T), (traj t).2.2 ∂Phase2.trajMeasure (Phase2.env₁_1 bp) alg (Phase2.env₁_1 bp).hr_meas T)) := by
      rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    have h_sum_sub : ∑ t : Fin T, (((1 / 2 + bp.Δ) - ∫ (traj : Phase2.Trajectory (Fin 2) Bool T), (traj t).2.2 ∂Phase2.trajMeasure (Phase2.env₁_0 bp) alg (Phase2.env₁_0 bp).hr_meas T) +
                                   ((1 / 2 + bp.Δ) - ∫ (traj : Phase2.Trajectory (Fin 2) Bool T), (traj t).2.2 ∂Phase2.trajMeasure (Phase2.env₁_1 bp) alg (Phase2.env₁_1 bp).hr_meas T)) =
                     ∑ t : Fin T, (2 * bp.Δ * ((Phase2.actionMarginal (Phase2.env₁_0 bp) alg (Phase2.env₁_0 bp).hr_meas (Phase2.env₁_0_isMarkov bp) hAlg T t) {1}).toReal +
                                   2 * bp.Δ * ((Phase2.actionMarginal (Phase2.env₁_1 bp) alg (Phase2.env₁_1 bp).hr_meas (Phase2.env₁_1_isMarkov bp) hAlg T t) {0}).toReal) := by
      apply Finset.sum_congr rfl
      intro t _
      rw [h_regret_step_0 T t, h_regret_step_1 T t]
    have h_sum_marg : ∑ t : Fin T, (2 * bp.Δ * ((Phase2.actionMarginal (Phase2.env₁_0 bp) alg (Phase2.env₁_0 bp).hr_meas (Phase2.env₁_0_isMarkov bp) hAlg T t) {1}).toReal +
                                    2 * bp.Δ * ((Phase2.actionMarginal (Phase2.env₁_1 bp) alg (Phase2.env₁_1 bp).hr_meas (Phase2.env₁_1_isMarkov bp) hAlg T t) {0}).toReal) =
                      ∑ t : Fin T, (2 * bp.Δ * ((Phase2.actionMarginal (Phase2.env₁_0 bp) alg (Phase2.env₁_0 bp).hr_meas (Phase2.env₁_0_isMarkov bp) hAlg (t.val + 1) ⟨t.val, Nat.lt_succ_self _⟩) {1}).toReal +
                                    2 * bp.Δ * ((Phase2.actionMarginal (Phase2.env₁_1 bp) alg (Phase2.env₁_1 bp).hr_meas (Phase2.env₁_1_isMarkov bp) hAlg (t.val + 1) ⟨t.val, Nat.lt_succ_self _⟩) {0}).toReal) := by
      apply Finset.sum_congr rfl
      intro t _
      rw [h_marginal_consist_0 T t, h_marginal_consist_1 T t]
    have h_sum_factor : ∑ t : Fin T, (2 * bp.Δ * ((Phase2.actionMarginal (Phase2.env₁_0 bp) alg (Phase2.env₁_0 bp).hr_meas (Phase2.env₁_0_isMarkov bp) hAlg (t.val + 1) ⟨t.val, Nat.lt_succ_self _⟩) {1}).toReal +
                                      2 * bp.Δ * ((Phase2.actionMarginal (Phase2.env₁_1 bp) alg (Phase2.env₁_1 bp).hr_meas (Phase2.env₁_1_isMarkov bp) hAlg (t.val + 1) ⟨t.val, Nat.lt_succ_self _⟩) {0}).toReal) =
                        ∑ t : Fin T, 2 * bp.Δ * (((Phase2.actionMarginal (Phase2.env₁_0 bp) alg (Phase2.env₁_0 bp).hr_meas (Phase2.env₁_0_isMarkov bp) hAlg (t.val + 1) ⟨t.val, Nat.lt_succ_self _⟩) {1}).toReal +
                                                 ((Phase2.actionMarginal (Phase2.env₁_1 bp) alg (Phase2.env₁_1 bp).hr_meas (Phase2.env₁_1_isMarkov bp) hAlg (t.val + 1) ⟨t.val, Nat.lt_succ_self _⟩) {0}).toReal) := by
      apply Finset.sum_congr rfl
      intro t _
      ring
    have h_sum_le_cam : ∑ t : Fin T, 2 * bp.Δ * (1 - miSeq (Phase2.env₁_0 bp) (Phase2.env₁_1 bp) alg (Phase2.env₁_0_isMarkov bp) (Phase2.env₁_1_isMarkov bp) hAlg t.val) ≤
                        ∑ t : Fin T, 2 * bp.Δ * (((Phase2.actionMarginal (Phase2.env₁_0 bp) alg (Phase2.env₁_0 bp).hr_meas (Phase2.env₁_0_isMarkov bp) hAlg (t.val + 1) ⟨t.val, Nat.lt_succ_self _⟩) {1}).toReal +
                                                 ((Phase2.actionMarginal (Phase2.env₁_1 bp) alg (Phase2.env₁_1 bp).hr_meas (Phase2.env₁_1_isMarkov bp) hAlg (t.val + 1) ⟨t.val, Nat.lt_succ_self _⟩) {0}).toReal) := by
      apply Finset.sum_le_sum
      intro t _
      apply mul_le_mul_of_nonneg_left (h_le_cam t.val)
      have h1 : 0 ≤ 2 * bp.Δ := by have h_d := bp.hΔ0; linarith
      exact h1
    have h_mi_le1 : ∀ t, miSeq (Phase2.env₁_0 bp) (Phase2.env₁_1 bp) alg (Phase2.env₁_0_isMarkov bp) (Phase2.env₁_1_isMarkov bp) hAlg t ≤ 1 := by
      intro t
      haveI inst1 : IsProbabilityMeasure (Phase2.actionMarginal (Phase2.env₁_0 bp) alg (Phase2.env₁_0 bp).hr_meas (Phase2.env₁_0_isMarkov bp) hAlg (t + 1) ⟨t, Nat.lt_succ_self t⟩) :=
        Phase2.actionMarginal_isProbability _ _ _ _ _ _ _
      haveI inst2 : IsProbabilityMeasure (Phase2.actionMarginal (Phase2.env₁_1 bp) alg (Phase2.env₁_1 bp).hr_meas (Phase2.env₁_1_isMarkov bp) hAlg (t + 1) ⟨t, Nat.lt_succ_self t⟩) :=
        Phase2.actionMarginal_isProbability _ _ _ _ _ _ _
      exact tvDistMeasure_le_one _ _
    have h_nonneg_term : ∀ i : Fin T, 0 ≤ 2 * bp.Δ * (1 - miSeq (Phase2.env₁_0 bp) (Phase2.env₁_1 bp) alg (Phase2.env₁_0_isMarkov bp) (Phase2.env₁_1_isMarkov bp) hAlg i.val) := by
      intro i
      have h1 : 0 ≤ 2 * bp.Δ := by have h_d := bp.hΔ0; linarith
      have h2 : miSeq (Phase2.env₁_0 bp) (Phase2.env₁_1 bp) alg (Phase2.env₁_0_isMarkov bp) (Phase2.env₁_1_isMarkov bp) hAlg i.val ≤ 1 := h_mi_le1 i.val
      nlinarith
    have h_split : ∑ t : Fin T, 2 * bp.Δ * (1 - miSeq (Phase2.env₁_0 bp) (Phase2.env₁_1 bp) alg (Phase2.env₁_0_isMarkov bp) (Phase2.env₁_1_isMarkov bp) hAlg t.val) ≥
        ∑ t ∈ Finset.univ.filter (fun i : Fin T => t₀ ≤ i.val), 2 * bp.Δ * (1 - miSeq (Phase2.env₁_0 bp) (Phase2.env₁_1 bp) alg (Phase2.env₁_0_isMarkov bp) (Phase2.env₁_1_isMarkov bp) hAlg t.val) := by
      have h_eq := Finset.sum_filter_add_sum_filter_not Finset.univ (fun (i : Fin T) => t₀ ≤ i.val) (fun i => 2 * bp.Δ * (1 - miSeq (Phase2.env₁_0 bp) (Phase2.env₁_1 bp) alg (Phase2.env₁_0_isMarkov bp) (Phase2.env₁_1_isMarkov bp) hAlg i.val))
      rw [← h_eq]
      apply le_add_of_nonneg_right
      apply Finset.sum_nonneg
      intro i _
      exact h_nonneg_term i
    have h_bound_tail : ∑ t ∈ Finset.univ.filter (fun i : Fin T => t₀ ≤ i.val), 2 * bp.Δ * (1 - miSeq (Phase2.env₁_0 bp) (Phase2.env₁_1 bp) alg (Phase2.env₁_0_isMarkov bp) (Phase2.env₁_1_isMarkov bp) hAlg t.val) ≥
                        ∑ t ∈ Finset.univ.filter (fun i : Fin T => t₀ ≤ i.val), 2 * bp.Δ * (1 - (B + η)) := by
      apply Finset.sum_le_sum
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      have h_lt := ht₀ i.val hi
      have h1 : 0 ≤ 2 * bp.Δ := by have h_d := bp.hΔ0; linarith
      have h2 : 1 - (B + η) ≤ 1 - miSeq (Phase2.env₁_0 bp) (Phase2.env₁_1 bp) alg (Phase2.env₁_0_isMarkov bp) (Phase2.env₁_1_isMarkov bp) hAlg i.val := by linarith
      exact mul_le_mul_of_nonneg_left h2 h1
    have h_card : (Finset.univ.filter (fun i : Fin T => t₀ ≤ i.val)).card = T - t₀ := by
      have hc : (Finset.univ.filter (fun i : Fin T => t₀ ≤ i.val)).card + (Finset.univ.filter (fun i : Fin T => i.val < t₀)).card = T := by
        have h_union : (Finset.univ.filter (fun i : Fin T => t₀ ≤ i.val)) ∪ (Finset.univ.filter (fun i : Fin T => i.val < t₀)) = Finset.univ := by
          ext x
          simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
          apply iff_true_intro
          omega
        have h_disj : Disjoint (Finset.univ.filter (fun i : Fin T => t₀ ≤ i.val)) (Finset.univ.filter (fun i : Fin T => i.val < t₀)) := by
          simp only [Finset.disjoint_left, Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
          intro x hx
          exact hx
        have h_sum := Finset.card_union_of_disjoint h_disj
        rw [h_union] at h_sum
        rw [← h_sum, Finset.card_univ, Fintype.card_fin]
      have hc2 : (Finset.univ.filter (fun i : Fin T => i.val < t₀)).card = t₀ := by
        let f_emb : Fin t₀ ↪ Fin T := ⟨fun i => ⟨i.val, by omega⟩, fun i j hij => by
          have h1 : (⟨i.val, by omega⟩ : Fin T).val = (⟨j.val, by omega⟩ : Fin T).val := congrArg Fin.val hij
          exact Fin.ext h1⟩
        have h_map : (Finset.univ : Finset (Fin t₀)).map f_emb = Finset.univ.filter (fun i : Fin T => i.val < t₀) := by
          ext x
          simp only [Finset.mem_map, Finset.mem_univ, true_and, Finset.mem_filter, f_emb, Function.Embedding.coeFn_mk]
          constructor
          · rintro ⟨i, rfl⟩
            exact i.isLt
          · intro hx
            refine ⟨⟨x.val, hx⟩, rfl⟩
        have hc3 := congrArg Finset.card h_map
        rw [Finset.card_map, Finset.card_univ, Fintype.card_fin] at hc3
        exact hc3.symm
      rw [hc2] at hc
      omega
    have h_sum_const : ∑ t ∈ Finset.univ.filter (fun i : Fin T => t₀ ≤ i.val), 2 * bp.Δ * (1 - (B + η)) =
                       ((T - t₀ : ℕ) : ℝ) * (2 * bp.Δ * (1 - (B + η))) := by
      rw [Finset.sum_const, h_card, nsmul_eq_mul]
    calc 2 * bp.Δ * (1 - (B + η)) * ((T - t₀ : ℕ) : ℝ)
      _ = ((T - t₀ : ℕ) : ℝ) * (2 * bp.Δ * (1 - (B + η))) := by ring
      _ = ∑ t ∈ Finset.univ.filter (fun i : Fin T => t₀ ≤ i.val), 2 * bp.Δ * (1 - (B + η)) := h_sum_const.symm
      _ ≤ ∑ t ∈ Finset.univ.filter (fun i : Fin T => t₀ ≤ i.val), 2 * bp.Δ * (1 - miSeq (Phase2.env₁_0 bp) (Phase2.env₁_1 bp) alg (Phase2.env₁_0_isMarkov bp) (Phase2.env₁_1_isMarkov bp) hAlg t.val) := h_bound_tail
      _ ≤ ∑ t : Fin T, 2 * bp.Δ * (1 - miSeq (Phase2.env₁_0 bp) (Phase2.env₁_1 bp) alg (Phase2.env₁_0_isMarkov bp) (Phase2.env₁_1_isMarkov bp) hAlg t.val) := h_split
      _ ≤ ∑ t : Fin T, 2 * bp.Δ * (((Phase2.actionMarginal (Phase2.env₁_0 bp) alg (Phase2.env₁_0 bp).hr_meas (Phase2.env₁_0_isMarkov bp) hAlg (t.val + 1) ⟨t.val, Nat.lt_succ_self _⟩) {1}).toReal + ((Phase2.actionMarginal (Phase2.env₁_1 bp) alg (Phase2.env₁_1 bp).hr_meas (Phase2.env₁_1_isMarkov bp) hAlg (t.val + 1) ⟨t.val, Nat.lt_succ_self _⟩) {0}).toReal) := h_sum_le_cam
      _ = ∑ t : Fin T, (2 * bp.Δ * ((Phase2.actionMarginal (Phase2.env₁_0 bp) alg (Phase2.env₁_0 bp).hr_meas (Phase2.env₁_0_isMarkov bp) hAlg (t.val + 1) ⟨t.val, Nat.lt_succ_self _⟩) {1}).toReal + 2 * bp.Δ * ((Phase2.actionMarginal (Phase2.env₁_1 bp) alg (Phase2.env₁_1 bp).hr_meas (Phase2.env₁_1_isMarkov bp) hAlg (t.val + 1) ⟨t.val, Nat.lt_succ_self _⟩) {0}).toReal) := h_sum_factor.symm
      _ = ∑ t : Fin T, (2 * bp.Δ * ((Phase2.actionMarginal (Phase2.env₁_0 bp) alg (Phase2.env₁_0 bp).hr_meas (Phase2.env₁_0_isMarkov bp) hAlg T t) {1}).toReal + 2 * bp.Δ * ((Phase2.actionMarginal (Phase2.env₁_1 bp) alg (Phase2.env₁_1 bp).hr_meas (Phase2.env₁_1_isMarkov bp) hAlg T t) {0}).toReal) := h_sum_marg.symm
      _ = ∑ t : Fin T, (((1 / 2 + bp.Δ) - ∫ (traj : Phase2.Trajectory (Fin 2) Bool T), (traj t).2.2 ∂Phase2.trajMeasure (Phase2.env₁_0 bp) alg (Phase2.env₁_0 bp).hr_meas T) + ((1 / 2 + bp.Δ) - ∫ (traj : Phase2.Trajectory (Fin 2) Bool T), (traj t).2.2 ∂Phase2.trajMeasure (Phase2.env₁_1 bp) alg (Phase2.env₁_1 bp).hr_meas T)) := h_sum_sub.symm
      _ = ((∑ _t : Fin T, (1 / 2 + bp.Δ)) - ∑ t : Fin T, ∫ (traj : Phase2.Trajectory (Fin 2) Bool T), (traj t).2.2 ∂Phase2.trajMeasure (Phase2.env₁_0 bp) alg (Phase2.env₁_0 bp).hr_meas T) + ((∑ _t : Fin T, (1 / 2 + bp.Δ)) - ∑ t : Fin T, ∫ (traj : Phase2.Trajectory (Fin 2) Bool T), (traj t).2.2 ∂Phase2.trajMeasure (Phase2.env₁_1 bp) alg (Phase2.env₁_1 bp).hr_meas T) := h_sum_combine.symm
      _ = regret (Phase2.env₁_0 bp) alg T + regret (Phase2.env₁_1 bp) alg T := h_regret_eq.symm
  use bp.Δ * (1 - (B + η))
  constructor
  · have h1 : 0 < bp.Δ := bp.hΔ0
    have h2 : B + η < 1 / 2 := hB_eta_lt_half
    nlinarith
  · apply Filter.eventually_atTop.mpr
    use 2 * t₀
    intro T hT
    have hT_pos : (0 : ℝ) ≤ (T : ℝ) := Nat.cast_nonneg T
    have hT_ge_t₀ : t₀ ≤ T := by omega
    have ht₀_le : (t₀ : ℝ) ≤ (T : ℝ) / 2 := by
      have h_real : 2 * (t₀ : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
      linarith
    have h_sub : (T : ℝ) / 2 ≤ ((T - t₀ : ℕ) : ℝ) := by
      have h_sub_cast : ((T - t₀ : ℕ) : ℝ) = (T : ℝ) - (t₀ : ℝ) := Nat.cast_sub hT_ge_t₀
      linarith
    have h_base := h_sum_regret T hT_ge_t₀
    calc bp.Δ * (1 - (B + η)) * (T : ℝ)
      _ = 2 * bp.Δ * (1 - (B + η)) * ((T : ℝ) / 2) := by ring
      _ ≤ 2 * bp.Δ * (1 - (B + η)) * ((T - t₀ : ℕ) : ℝ) := by
            apply mul_le_mul_of_nonneg_left h_sub
            have h1 : 0 < bp.Δ := bp.hΔ0
            have h2 : B + η < 1 / 2 := hB_eta_lt_half
            nlinarith
      _ ≤ regret (Phase2.env₁_0 bp) alg T + regret (Phase2.env₁_1 bp) alg T := h_base

theorem possesses_x1_avoids_x1_failure
    {Sig : Type*} [MeasurableSpace Sig] [TopologicalSpace Sig] [BorelSpace Sig]
    [MeasurableSingletonClass Sig] [MeasurableEq Sig]
    (bp : Phase2.BanditParam)
    (alg : SixPrimitives.Algorithm (Fin 2) Bool Sig)
    (hAlg : Phase2.AlgIsMarkov alg)
    (hPoss : PossessesX₁ (miSeq
                (Phase2.env₁_0 bp) (Phase2.env₁_1 bp) alg
                (Phase2.env₁_0_isMarkov bp)
                (Phase2.env₁_1_isMarkov bp)
                hAlg)) :
    ¬ LacksX₁ (miSeq
                (Phase2.env₁_0 bp) (Phase2.env₁_1 bp) alg
                (Phase2.env₁_0_isMarkov bp)
                (Phase2.env₁_1_isMarkov bp)
                hAlg) :=
  hPoss

end NecessityX1

/-! # §2  Necessity of X₂ — Cross-Context Safety Transfer -/

section NecessityX2

lemma measurableSet_survivedToStep (K : ℕ) (hK : 0 < K) (k : ℕ) :
    MeasurableSet (Phase2.survivedToStep K hK k) := by
  dsimp [Phase2.survivedToStep]
  -- Reshape the set-builder notation into a formal preimage for the unifier
  change MeasurableSet ((fun ω => Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans ω k) ⁻¹' {Fin.last (K + 1)}ᶜ)
  apply MeasurableSet.preimage
  · apply MeasurableSet.compl
    apply measurableSet_singleton
  · exact Phase2.measurable_state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans (k + 1) k

lemma measurableSet_dangerAndSurvival (K : ℕ) (hK : 0 < K) (k : ℕ) (aDanger : Fin (K + 2) → Fin 2) :
    MeasurableSet (Phase2.survivedToStep K hK k ∩
      { ω : Phase2.Trajectory (Fin 2) (Fin (K + 2)) (k + 1) |
        (ω ⟨k, Nat.lt_succ_self k⟩).1 =
          aDanger (Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans ω k) }) := by
  apply MeasurableSet.inter
  · exact measurableSet_survivedToStep K hK k
  · have h_eq : { ω : Phase2.Trajectory (Fin 2) (Fin (K + 2)) (k + 1) | (ω ⟨k, Nat.lt_succ_self k⟩).1 = aDanger (Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans ω k) } =
      ⋃ (a : Fin 2), {ω | (ω ⟨k, Nat.lt_succ_self k⟩).1 = a} ∩ {ω | aDanger (Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans ω k) = a} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
      constructor
      · intro h
        exact ⟨(ω ⟨k, Nat.lt_succ_self k⟩).1, rfl, h.symm⟩
      · rintro ⟨a, h1, h2⟩
        rw [h1, h2]
    rw [h_eq]
    apply MeasurableSet.iUnion
    intro a
    apply MeasurableSet.inter
    · have h_lhs : Measurable (fun ω : Phase2.Trajectory (Fin 2) (Fin (K + 2)) (k + 1) => (ω ⟨k, Nat.lt_succ_self k⟩).1) :=
        Phase2.measurable_traj_action k (Nat.lt_succ_self k)
      exact h_lhs (measurableSet_singleton a)
    · have h_rhs : Measurable (fun ω : Phase2.Trajectory (Fin 2) (Fin (K + 2)) (k + 1) => aDanger (Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans ω k)) :=
        Measurable.comp (measurable_of_finite _) (Phase2.measurable_state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans (k + 1) k)
      exact h_rhs (measurableSet_singleton a)

lemma env₂_transFn_eq (K : ℕ) (hK : 0 < K) (s : Fin (K + 2)) (a : Fin 2) :
    (Phase2.env₂_isDet K hK).toTrans.transFn (s, a) =
    if h : s.val < K then if a = 0 then ⟨s.val + 1, by omega⟩ else ⟨K + 1, by omega⟩ else s := rfl

lemma env₂_state_t_le_time (K : ℕ) (hK : 0 < K) {T : ℕ} (ω : Phase2.Trajectory (Fin 2) (Fin (K + 2)) T) (t : ℕ) (ht : t ≤ T) :
    (Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans ω t).val ≤ t ∨
    Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans ω t = Fin.last (K + 1) := by
  induction t with
  | zero =>
    left
    rw [Phase2.state_t_zero]
    exact Nat.le_refl 0
  | succ t ih =>
    have h_lt : t < T := by omega
    rw [Phase2.state_t_succ _ _ _ t h_lt]
    have ih' := ih (by omega)
    set s := Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans ω t
    set a := (ω ⟨t, h_lt⟩).1
    rw [env₂_transFn_eq]
    rcases ih' with h_le | h_trap
    · split_ifs
      · left; simp; omega
      · right; rfl
      · left; omega
    · rw [h_trap]
      have h_not_lt : ¬ ((Fin.last (K + 1)).val < K) := by
        have : (Fin.last (K + 1)).val = K + 1 := rfl
        omega
      rw [dif_neg h_not_lt]
      right; rfl

lemma env₂_survived_val_lt (K : ℕ) (hK : 0 < K) {T : ℕ} (ω : Phase2.Trajectory (Fin 2) (Fin (K + 2)) T) (t : ℕ) (ht_le : t ≤ T) (ht_lt : t < K)
    (h_surv : Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans ω t ≠ Fin.last (K + 1)) :
    (Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans ω t).val < K := by
  have h_inv := env₂_state_t_le_time K hK ω t ht_le
  rcases h_inv with h_le | h_trap
  · exact Nat.lt_of_le_of_lt h_le ht_lt
  · contradiction

lemma env₂_transFn_danger (K : ℕ) (hK : 0 < K) (s : Fin (K + 2)) (h_lt : s.val < K) :
    (Phase2.env₂_isDet K hK).toTrans.transFn (s, 1) = Fin.last (K + 1) := by
  rw [env₂_transFn_eq]
  rw [dif_pos h_lt]
  have h_neq : (1 : Fin 2) ≠ 0 := by decide
  rw [if_neg h_neq]
  rfl

lemma env₂_transFn_safe (K : ℕ) (hK : 0 < K) (s : Fin (K + 2)) (h_lt : s.val < K) :
    (Phase2.env₂_isDet K hK).toTrans.transFn (s, 0) ≠ Fin.last (K + 1) := by
  rw [env₂_transFn_eq]
  rw [dif_pos h_lt, if_pos rfl]
  intro h_eq
  have h_val : (⟨s.val + 1, by omega⟩ : Fin (K + 2)).val = (Fin.last (K + 1)).val := congrArg Fin.val h_eq
  revert h_val
  simp [Fin.last]; omega

lemma env₂_transFn_trap (K : ℕ) (hK : 0 < K) (a : Fin 2) :
    (Phase2.env₂_isDet K hK).toTrans.transFn (Fin.last (K + 1), a) = Fin.last (K + 1) := by
  rw [env₂_transFn_eq]
  have h_not_lt : ¬ ((Fin.last (K + 1)).val < K) := by
    have : (Fin.last (K + 1)).val = K + 1 := rfl
    omega
  rw [dif_neg h_not_lt]

lemma survivedToStep_succ_eq (K : ℕ) (hK : 0 < K) (k : ℕ) (hk_lt : k < K) :
    Phase2.survivedToStep K hK (k + 1) =
    { ω : Phase2.Trajectory (Fin 2) (Fin (K + 2)) (k + 2) |
      Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans ω k ≠ Fin.last (K + 1) } \
    { ω : Phase2.Trajectory (Fin 2) (Fin (K + 2)) (k + 2) |
      (ω ⟨k, by omega⟩).1 = 1 } := by
  ext ω
  simp only [Phase2.survivedToStep, Set.mem_diff, Set.mem_setOf_eq]
  have h_succ : Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans ω (k + 1) =
    (Phase2.env₂_isDet K hK).toTrans.transFn (Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans ω k, (ω ⟨k, by omega⟩).1) := Phase2.state_t_succ _ _ _ k (by omega)
  rw [h_succ]
  constructor
  · intro h_surv_succ
    by_cases h_surv_k : Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans ω k = Fin.last (K + 1)
    · exfalso
      apply h_surv_succ
      rw [h_surv_k]
      exact env₂_transFn_trap K hK _
    · refine ⟨h_surv_k, ?_⟩
      intro h_danger
      apply h_surv_succ
      have h_val_lt := env₂_survived_val_lt K hK ω k (by omega) hk_lt h_surv_k
      rw [h_danger]
      exact env₂_transFn_danger K hK _ h_val_lt
  · rintro ⟨h_surv_k, h_not_danger⟩
    have h_val_lt := env₂_survived_val_lt K hK ω k (by omega) hk_lt h_surv_k
    have h_safe : (ω ⟨k, by omega⟩).1 = 0 := by
      have h_lt := (ω ⟨k, by omega⟩).1.isLt
      have h_nd : (ω ⟨k, by omega⟩).1.val ≠ 1 := by
        intro h
        apply h_not_danger
        ext
        exact h
      ext
      omega
    rw [h_safe]
    exact env₂_transFn_safe K hK _ h_val_lt

lemma survivalProbSeq_zero
    {Sig : Type*} [MeasurableSpace Sig] [TopologicalSpace Sig] [BorelSpace Sig]
    (K : ℕ) (hK : 0 < K)
    (alg : SixPrimitives.Algorithm (Fin 2) (Fin (K + 2)) Sig)
    (hAlg : Phase2.AlgIsMarkov alg) :
    Phase2.survivalProbSeq K hK alg hAlg 0 = 1 := by
  unfold Phase2.survivalProbSeq
  have h_univ : Phase2.survivedToStep K hK 0 = Set.univ := by
    ext ω
    simp only [Phase2.survivedToStep, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    rw [Phase2.state_t_zero]
    intro h_eq
    have h_val : (0 : ℕ) = (Fin.last (K + 1)).val := congrArg Fin.val h_eq
    revert h_val
    simp [Fin.last]
  rw [h_univ]
  have hEnvMarkov : Phase2.EnvIsMarkov (Phase2.env₂ K hK) :=
    Phase2.envIsDeterministic_isMarkov (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK)
  haveI h_prob : IsProbabilityMeasure (Phase2.trajMeasure (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas 1) :=
    Phase2.trajMeasure_isProbability (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas hEnvMarkov hAlg 1
  rw [measure_univ]
  exact ENNReal.toReal_one

noncomputable def env₂_potential (K : ℕ) (s : Fin (K + 2)) : ℝ :=
  if s = Fin.last (K + 1) then (K : ℝ) else (s.val : ℝ)

lemma env₂_state_absorbing_trap (K : ℕ) (hK : 0 < K) (s : Fin (K + 2)) (a : Fin 2)
    (hs : s = Fin.last (K + 1)) :
    (Phase2.env₂_isDet K hK).toTrans.transFn (s, a) = Fin.last (K + 1) := by
  rw [env₂_transFn_eq]
  have h_not_lt : ¬ (s.val < K) := by
    have h_val : s.val = K + 1 := congrArg Fin.val hs
    omega
  rw [dif_neg h_not_lt]
  exact hs

lemma env₂_state_t_eq_trap_implies_future (K : ℕ) (hK : 0 < K) {T : ℕ}
    (ω : Phase2.Trajectory (Fin 2) (Fin (K + 2)) T) (t d : ℕ) (htd : t + d ≤ T)
    (h_eq : Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans ω t = Fin.last (K + 1)) :
    Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans ω (t + d) = Fin.last (K + 1) := by
  induction d with
  | zero => exact h_eq
  | succ d ih =>
    have h_td : t + d < T := by omega
    have ih_val := ih (by omega)
    have h_succ : Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans ω (t + d + 1) =
      (Phase2.env₂_isDet K hK).toTrans.transFn (Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans ω (t + d), (ω ⟨t + d, h_td⟩).1) := Phase2.state_t_succ _ _ _ (t + d) h_td
    have h_time : t + (d + 1) = t + d + 1 := by omega
    rw [h_time]
    rw [h_succ, ih_val]
    exact env₂_state_absorbing_trap K hK _ _ rfl

lemma env₂_state_absorbing_K (K : ℕ) (hK : 0 < K) (s : Fin (K + 2)) (a : Fin 2)
    (hs : s.val = K) :
    ((Phase2.env₂_isDet K hK).toTrans.transFn (s, a)).val = K := by
  rw [env₂_transFn_eq]
  have h_not_lt : ¬ (s.val < K) := by omega
  rw [dif_neg h_not_lt]
  exact hs

lemma env₂_state_t_eq_K_implies_future (K : ℕ) (hK : 0 < K) {T : ℕ}
    (ω : Phase2.Trajectory (Fin 2) (Fin (K + 2)) T) (t d : ℕ) (htd : t + d ≤ T)
    (h_eq : (Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans ω t).val = K) :
    (Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans ω (t + d)).val = K := by
  induction d with
  | zero => exact h_eq
  | succ d ih =>
    have h_td : t + d < T := by omega
    have ih_val := ih (by omega)
    have h_succ : Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans ω (t + d + 1) =
      (Phase2.env₂_isDet K hK).toTrans.transFn (Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans ω (t + d), (ω ⟨t + d, h_td⟩).1) := Phase2.state_t_succ _ _ _ (t + d) h_td
    have h_time : t + (d + 1) = t + d + 1 := by omega
    rw [h_time]
    rw [h_succ]
    exact env₂_state_absorbing_K K hK _ _ ih_val

lemma env₂_never_K_of_trap (K : ℕ) (hK : 0 < K) {T : ℕ}
    (ω : Phase2.Trajectory (Fin 2) (Fin (K + 2)) T) (hT : K ≤ T)
    (h_trap : Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans ω K = Fin.last (K + 1))
    (t : ℕ) (ht : t ≤ T) :
    (Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans ω t).val ≠ K := by
  intro h_eq
  by_cases h_le : t ≤ K
  · have h_future := env₂_state_t_eq_K_implies_future K hK ω t (K - t) (by omega) h_eq
    have h_rewrite : t + (K - t) = K := by omega
    rw [h_rewrite] at h_future
    have h_trap_val : (Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans ω K).val = K + 1 := by rw [h_trap]; rfl
    linarith
  · have h_future := env₂_state_t_eq_trap_implies_future K hK ω K (t - K) (by omega) h_trap
    have h_rewrite : K + (t - K) = t := by omega
    rw [h_rewrite] at h_future
    have h_future_val : (Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans ω t).val = K + 1 := by rw [h_future]; rfl
    linarith

lemma env₂_reward_le_potential_diff (K : ℕ) (hK : 0 < K) (s : Fin (K + 2)) (a : Fin 2)
    (h_not_K : s.val ≠ K) :
    (Phase2.env₂ K hK).r (s, a) ≤ env₂_potential K ((Phase2.env₂_isDet K hK).toTrans.transFn (s, a)) - env₂_potential K s := by
  by_cases hs_trap : s = Fin.last (K + 1)
  · rw [hs_trap]
    have h_trans := env₂_state_absorbing_trap K hK (Fin.last (K + 1)) a rfl
    rw [h_trans]
    dsimp [Phase2.env₂]
    unfold env₂_potential
    have h_not_lt : ¬ ((Fin.last (K + 1)).val < K) := by
      have h_val : (Fin.last (K + 1)).val = K + 1 := rfl
      omega
    have h_not_eq : ¬ ((Fin.last (K + 1)).val = K) := by
      have h_val : (Fin.last (K + 1)).val = K + 1 := rfl
      omega
    simp
  · have hs_lt : s.val < K := by
      have h_bound := s.isLt
      have h_ne : s.val ≠ K + 1 := by
        intro h
        apply hs_trap
        ext
        exact h
      omega
    rw [env₂_transFn_eq]
    rw [dif_pos hs_lt]
    by_cases ha : a = 0
    · rw [if_pos ha]
      unfold env₂_potential
      rw [if_neg hs_trap]
      have h_next : (⟨s.val + 1, by omega⟩ : Fin (K + 2)) ≠ Fin.last (K + 1) := by
        intro h
        have h_val : s.val + 1 = K + 1 := congrArg Fin.val h
        omega
      rw [if_neg h_next]
      dsimp [Phase2.env₂]
      simp [hs_lt]
      rw [if_pos ha]
    · have ha1 : a = 1 := by
        revert ha
        fin_cases a <;> simp
      rw [ha1]
      have h_one_ne_zero : (1 : Fin 2) ≠ 0 := by decide
      rw [if_neg h_one_ne_zero]
      unfold env₂_potential
      rw [if_neg hs_trap]
      have h_next_eq : (⟨K + 1, by omega⟩ : Fin (K + 2)) = Fin.last (K + 1) := rfl
      rw [if_pos h_next_eq]
      dsimp [Phase2.env₂]
      simp [hs_lt]
      have h_cast : (s.val : ℝ) < K := by exact_mod_cast hs_lt
      linarith

lemma env₂_sum_reward_le_potential_diff (K : ℕ) (hK : 0 < K) {T : ℕ}
    (ω : Phase2.Trajectory (Fin 2) (Fin (K + 2)) T) (hT : K ≤ T)
    (h_trap : Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans ω K = Fin.last (K + 1)) :
    ∑ t : Fin T, (Phase2.env₂ K hK).r (Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans ω t.val, (ω t).1) ≤
    env₂_potential K (Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans ω T) -
    env₂_potential K (Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans ω 0) := by
  have h_le_diff : ∀ t : Fin T, (Phase2.env₂ K hK).r (Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans ω t.val, (ω t).1) ≤
      env₂_potential K (Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans ω (t.val + 1)) -
      env₂_potential K (Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans ω t.val) := by
    intro t
    have h_not_K := env₂_never_K_of_trap K hK ω hT h_trap t.val (by omega)
    have h_step := env₂_reward_le_potential_diff K hK _ (ω t).1 h_not_K
    have h_succ : Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans ω (t.val + 1) =
      (Phase2.env₂_isDet K hK).toTrans.transFn (Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans ω t.val, (ω t).1) := Phase2.state_t_succ _ _ _ t.val t.isLt
    rw [h_succ]
    exact h_step
  calc ∑ t : Fin T, (Phase2.env₂ K hK).r (Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans ω t.val, (ω t).1)
    _ ≤ ∑ t : Fin T, (env₂_potential K (Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans ω (t.val + 1)) - env₂_potential K (Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans ω t.val)) := Finset.sum_le_sum (fun t _ => h_le_diff t)
    _ = env₂_potential K (Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans ω T) - env₂_potential K (Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans ω 0) := by
      have h_tele_gen : ∀ (n : ℕ) (f : ℕ → ℝ), ∑ t : Fin n, (f (t.val + 1) - f t.val) = f n - f 0 := by
        intro n f
        induction n with
        | zero => simp
        | succ n ih =>
          rw [Fin.sum_univ_castSucc]
          simp_rw [Fin.val_castSucc]
          rw [ih]
          have h_last : (Fin.last n).val = n := rfl
          rw [h_last]
          ring
      exact h_tele_gen T (fun t => env₂_potential K (Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans ω t))

lemma env₂_reward_bound_on_absorption (K : ℕ) (hK : 0 < K) {T : ℕ}
    (ω : Phase2.Trajectory (Fin 2) (Fin (K + 2)) T) (hT : K ≤ T)
    (h_trap : Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans ω K = Fin.last (K + 1)) :
    ∑ t : Fin T, (Phase2.env₂ K hK).r (Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans ω t.val, (ω t).1) ≤ K := by
  have h_bound := env₂_sum_reward_le_potential_diff K hK ω hT h_trap
  have h_start : Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans ω 0 = (Phase2.env₂_isDet K hK).toTrans.s₀ := Phase2.state_t_zero _ _ _
  have h_pot_start : env₂_potential K (Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans ω 0) = 0 := by
    rw [h_start]
    unfold env₂_potential
    have h_not_trap : ¬ ((Phase2.env₂_isDet K hK).toTrans.s₀ = Fin.last (K + 1)) := by
      intro h
      have h_val : (Phase2.env₂_isDet K hK).toTrans.s₀.val = K + 1 := congrArg Fin.val h
      have h_s0_val : (Phase2.env₂_isDet K hK).toTrans.s₀.val = 0 := rfl
      rw [h_s0_val] at h_val
      omega
    simp [h_not_trap]
  have h_end_trap : Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans ω T = Fin.last (K + 1) := by
    have h_future := env₂_state_t_eq_trap_implies_future K hK ω K (T - K) (by omega) h_trap
    have h_rewrite : K + (T - K) = T := by omega
    rw [h_rewrite] at h_future
    exact h_future
  have h_pot_end : env₂_potential K (Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans ω T) = K := by
    unfold env₂_potential
    simp [h_end_trap]
  linarith

lemma env₂_integral_split
    {Sig : Type*} [MeasurableSpace Sig] [TopologicalSpace Sig] [BorelSpace Sig]
    (K : ℕ) (hK : 0 < K) (T : ℕ)
    (alg : SixPrimitives.Algorithm (Fin 2) (Fin (K + 2)) Sig)
    (f : Phase2.Trajectory (Fin 2) (Fin (K + 2)) T → ℝ)
    (hf_int : Integrable f (Phase2.trajMeasure (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas T)) :
    ∫ ω, f ω ∂Phase2.trajMeasure (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas T =
    ∫ ω in {ω | Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans ω K = Fin.last (K + 1)}, f ω ∂Phase2.trajMeasure (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas T +
    ∫ ω in {ω | Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans ω K ≠ Fin.last (K + 1)}, f ω ∂Phase2.trajMeasure (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas T := by
  have h_meas_eq : MeasurableSet {ω : Phase2.Trajectory (Fin 2) (Fin (K + 2)) T | Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans ω K = Fin.last (K + 1)} :=
    (Phase2.measurable_state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans T K) (measurableSet_singleton _)
  have h_comp : {ω : Phase2.Trajectory (Fin 2) (Fin (K + 2)) T | Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans ω K ≠ Fin.last (K + 1)} =
    {ω : Phase2.Trajectory (Fin 2) (Fin (K + 2)) T | Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans ω K = Fin.last (K + 1)}ᶜ := rfl
  rw [h_comp]
  exact (MeasureTheory.integral_add_compl h_meas_eq hf_int).symm

noncomputable def env₂_dangerAction (K : ℕ) : Fin (K + 2) → Fin 2 :=
  fun _ => 1

theorem necessity_x2
    {Sig : Type*} [MeasurableSpace Sig] [TopologicalSpace Sig] [BorelSpace Sig]
    [MeasurableSingletonClass Sig] [MeasurableEq Sig]
    (K : ℕ) (hK : 0 < K)
    (alg : SixPrimitives.Algorithm (Fin 2) (Fin (K + 2)) Sig)
    (hAlg : Phase2.AlgIsMarkov alg)
    (δ : ℝ) (hδ_pos : 0 < δ) (hδ_le_one : δ ≤ 1)
    (h_cond : ∀ k,
        Phase2.condDangerProbSeq K hK alg hAlg (env₂_dangerAction K) k ≥ δ) :
    LinearRegret (Phase2.env₂ K hK) alg := by
  unfold LinearRegret
  have hδ_sub_nonneg : (0 : ℝ) ≤ 1 - δ := by linarith
  have hδ_sub_lt_one : 1 - δ < 1 := by linarith
  have hc_def : 0 < 1 - (1 - δ) ^ K := by
    have h_pow_lt_one : (1 - δ) ^ K < 1 := by
      have H : ∀ n : ℕ, 0 < n → (1 - δ) ^ n < 1 := by
        intro n
        induction n with
        | zero => intro hn; exact False.elim (Nat.lt_irrefl 0 hn)
        | succ k ih =>
          intro _
          by_cases hk : k = 0
          · subst hk
            simp only [pow_succ, pow_zero, one_mul]
            exact hδ_sub_lt_one
          · have hk_pos : 0 < k := Nat.pos_of_ne_zero hk
            have ih_val : (1 - δ) ^ k < 1 := ih hk_pos
            calc (1 - δ) ^ (k + 1)
              _ = (1 - δ) ^ k * (1 - δ) := pow_succ (1 - δ) k
              _ ≤ 1 * (1 - δ) := mul_le_mul_of_nonneg_right ih_val.le hδ_sub_nonneg
              _ = 1 - δ       := one_mul _
              _ < 1            := hδ_sub_lt_one
      exact H K hK
    exact sub_pos.mpr h_pow_lt_one
  use 1 - (1 - δ) ^ K
  refine ⟨hc_def, ?_⟩
  use K
  apply Filter.eventually_atTop.mpr
  use K + 1
  intro T hT
  have hT_K : K ≤ T := by omega
  have h_opt : SixPrimitives.optValue (Phase2.env₂ K hK) T = T := Phase2.env₂_optValue K hK T
  have h_ind : ∀ k ≤ K, Phase2.survivalProbSeq K hK alg hAlg k ≤ (1 - δ) ^ k := by
    intro k
    induction k with
    | zero =>
      intro _
      rw [survivalProbSeq_zero K hK alg hAlg]
      simp
    | succ k ih =>
      intro hk_le
      have hk_le_K : k ≤ K := by omega
      have ih_val := ih hk_le_K
      have h_recurrence : Phase2.survivalProbSeq K hK alg hAlg (k + 1) ≤ (1 - δ) * Phase2.survivalProbSeq K hK alg hAlg k := by
        have h_cond_k := h_cond k
        change (if Phase2.survivalProbSeq K hK alg hAlg k = 0 then 0 else Phase2.dangerAndSurvivalProbSeq K hK alg hAlg (env₂_dangerAction K) k / Phase2.survivalProbSeq K hK alg hAlg k) ≥ δ at h_cond_k
        split_ifs at h_cond_k with h_zero
        · rw [h_zero]
          have h_pos : (0:ℝ) ≤ 1 - δ := hδ_sub_nonneg
          linarith
        · have h_div : Phase2.dangerAndSurvivalProbSeq K hK alg hAlg (env₂_dangerAction K) k ≥ δ * Phase2.survivalProbSeq K hK alg hAlg k := by
            have hp_nonneg : 0 ≤ Phase2.survivalProbSeq K hK alg hAlg k := ENNReal.toReal_nonneg
            have hp_pos : 0 < Phase2.survivalProbSeq K hK alg hAlg k := lt_of_le_of_ne hp_nonneg (Ne.symm h_zero)
            exact (le_div_iff₀ hp_pos).mp h_cond_k
          have hp_sub : Phase2.survivalProbSeq K hK alg hAlg (k + 1) ≤ Phase2.survivalProbSeq K hK alg hAlg k - Phase2.dangerAndSurvivalProbSeq K hK alg hAlg (env₂_dangerAction K) k := by
            unfold Phase2.survivalProbSeq Phase2.dangerAndSurvivalProbSeq
            have hk_lt : k < K := by omega
            have h_state_eq : ∀ (ω : Phase2.Trajectory (Fin 2) (Fin (K + 2)) (k + 2)) (t : ℕ) (ht : t ≤ k + 1),
              Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans (fun i : Fin (k + 1) => ω (Fin.castSucc i)) t =
              Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans ω t := by
              intro ω t ht
              induction t with
              | zero => rfl
              | succ t ih_t =>
                have ht_lt : t < k + 1 := by omega
                have ht_lt2 : t < k + 2 := by omega
                rw [Phase2.state_t_succ _ _ _ t ht_lt, Phase2.state_t_succ _ _ _ t ht_lt2, ih_t (by omega)]
                rfl
            have hEnvMarkov : Phase2.EnvIsMarkov (Phase2.env₂ K hK) := Phase2.envIsDeterministic_isMarkov _ (Phase2.env₂_isDet K hK)
            let surv_k := Phase2.survivedToStep K hK k
            let danger_k := { ω : Phase2.Trajectory (Fin 2) (Fin (K + 2)) (k + 1) | (ω ⟨k, Nat.lt_succ_self k⟩).1 = env₂_dangerAction K (Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans ω k) }
            have h_meas_surv : MeasurableSet surv_k := measurableSet_survivedToStep K hK k
            have h_meas_inter : MeasurableSet (surv_k ∩ danger_k) := measurableSet_dangerAndSurvival K hK k (env₂_dangerAction K)
            have h_trunc_surv := Phase2.trajMeasure_truncation_one (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas hEnvMarkov hAlg (k + 1) surv_k h_meas_surv
            have h_trunc_inter := Phase2.trajMeasure_truncation_one (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas hEnvMarkov hAlg (k + 1) (surv_k ∩ danger_k) h_meas_inter
            let A := { ω : Phase2.Trajectory (Fin 2) (Fin (K + 2)) (k + 2) | Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans ω k ≠ Fin.last (K + 1) }
            let B := { ω : Phase2.Trajectory (Fin 2) (Fin (K + 2)) (k + 2) | (ω ⟨k, by omega⟩).1 = 1 }
            have hA_eq : { ω : Phase2.Trajectory (Fin 2) (Fin (K + 2)) (k + 2) | (fun i => ω (Fin.castSucc i)) ∈ surv_k } = A := by
              ext ω
              simp only [Set.mem_setOf_eq, surv_k, Phase2.survivedToStep, A]
              rw [h_state_eq ω k (by omega)]
            have hAB_eq : { ω : Phase2.Trajectory (Fin 2) (Fin (K + 2)) (k + 2) | (fun i => ω (Fin.castSucc i)) ∈ surv_k ∩ danger_k } = A ∩ B := by
              ext ω
              simp only [Set.mem_inter_iff, Set.mem_setOf_eq, surv_k, danger_k, Phase2.survivedToStep, A, B]
              rw [h_state_eq ω k (by omega)]
              rfl
            rw [hA_eq] at h_trunc_surv
            rw [hAB_eq] at h_trunc_inter
            have h_succ_eq := survivedToStep_succ_eq K hK k hk_lt
            have h_meas_A : MeasurableSet A := by
              change MeasurableSet ((fun ω => Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans ω k) ⁻¹' {Fin.last (K + 1)}ᶜ)
              apply MeasurableSet.preimage
              · exact MeasurableSet.compl (measurableSet_singleton _)
              · exact Phase2.measurable_state_t _ _ _ _
            have h_meas_B : MeasurableSet B := by
              have h_action : Measurable (fun ω : Phase2.Trajectory (Fin 2) (Fin (K + 2)) (k + 2) => (ω ⟨k, by omega⟩).1) := Phase2.measurable_traj_action k (by omega)
              exact h_action (measurableSet_singleton 1)
            have h_meas_AB : MeasurableSet (A ∩ B) := MeasurableSet.inter h_meas_A h_meas_B
            let μ_k2 := Phase2.trajMeasure (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas (k + 2)
            have h_diff_set : A \ B = A \ (A ∩ B) := by
              ext x
              simp only [Set.mem_diff, Set.mem_inter_iff, not_and]
              tauto
            rw [h_diff_set] at h_succ_eq
            rw [h_succ_eq]
            haveI h_prob : IsProbabilityMeasure μ_k2 := Phase2.trajMeasure_isProbability _ _ _ hEnvMarkov hAlg (k + 2)
            have h_subset : A ∩ B ⊆ A := Set.inter_subset_left
            have h_mono : μ_k2 (A ∩ B) ≤ μ_k2 A := measure_mono h_subset
            have h_diff := measure_diff h_subset h_meas_AB.nullMeasurableSet (measure_ne_top μ_k2 (A ∩ B))
            have h_meas_val : μ_k2 (A \ (A ∩ B)) = μ_k2 A - μ_k2 (A ∩ B) := h_diff
            rw [h_meas_val]
            have h_toReal_sub : (μ_k2 A - μ_k2 (A ∩ B)).toReal = (μ_k2 A).toReal - (μ_k2 (A ∩ B)).toReal := by
              exact ENNReal.toReal_sub_of_le h_mono (measure_ne_top _ _)
            rw [h_toReal_sub, h_trunc_surv, h_trunc_inter]
          linarith
      calc Phase2.survivalProbSeq K hK alg hAlg (k + 1)
        _ ≤ (1 - δ) * Phase2.survivalProbSeq K hK alg hAlg k := h_recurrence
        _ ≤ (1 - δ) * (1 - δ) ^ k := mul_le_mul_of_nonneg_left ih_val hδ_sub_nonneg
        _ = (1 - δ) ^ (k + 1) := by ring
  have h_pK_bound : Phase2.survivalProbSeq K hK alg hAlg K ≤ (1 - δ) ^ K := h_ind K (by rfl)
  have h_regret_def : regret (Phase2.env₂ K hK) alg T = (T : ℝ) - algValue (Phase2.env₂ K hK) alg T := by
    unfold regret
    rw [h_opt]
  have h_algValue_bound : algValue (Phase2.env₂ K hK) alg T ≤ (T : ℝ) * Phase2.survivalProbSeq K hK alg hAlg K + (K : ℝ) * (1 - Phase2.survivalProbSeq K hK alg hAlg K) := by
    unfold algValue Phase2.algValue'
    let f : Phase2.Trajectory (Fin 2) (Fin (K + 2)) T → ℝ := fun ω => ∑ t : Fin T, (ω t).2.2
    have hEnvMarkov : Phase2.EnvIsMarkov (Phase2.env₂ K hK) := Phase2.envIsDeterministic_isMarkov _ (Phase2.env₂_isDet K hK)
    have h_ae_all : ∀ᵐ ω ∂Phase2.trajMeasure (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas T, ∀ t : Fin T, (ω t).2.2 = (Phase2.env₂ K hK).r (Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans ω t.val, (ω t).1) := by
      rw [ae_all_iff]
      intro t
      exact Phase2.trajMeasure_step_reward_eq (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas (Phase2.env₂_isDet K hK).toTrans hEnvMarkov hAlg T t.val t.isLt
    have hf_int : Integrable f (Phase2.trajMeasure (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas T) := by
      have h_meas : Measurable f := by
        dsimp [f]
        apply Finset.measurable_sum
        intro t _
        exact Measurable.snd (Measurable.snd (measurable_pi_apply t))
      have h_bound_ae : ∀ᵐ ω ∂Phase2.trajMeasure (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas T, ‖f ω‖ ≤ ‖(T : ℝ)‖ := by
        filter_upwards [h_ae_all] with ω h_rew
        dsimp [f]
        have h_sum_le : ∑ t : Fin T, (ω t).2.2 ≤ T := by
          calc ∑ t : Fin T, (ω t).2.2
            _ = ∑ t : Fin T, (Phase2.env₂ K hK).r (Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans ω t.val, (ω t).1) := Finset.sum_congr rfl (fun t _ => h_rew t)
            _ ≤ ∑ t : Fin T, (1 : ℝ) := by
              apply Finset.sum_le_sum
              intro t _
              dsimp [Phase2.env₂]
              split_ifs <;> norm_num
            _ = T := by simp
        have h_sum_nonneg : 0 ≤ ∑ t : Fin T, (ω t).2.2 := by
          rw [show ∑ t : Fin T, (ω t).2.2 = ∑ t : Fin T, (Phase2.env₂ K hK).r (Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans ω t.val, (ω t).1) from Finset.sum_congr rfl (fun t _ => h_rew t)]
          apply Finset.sum_nonneg
          intro t _
          dsimp [Phase2.env₂]
          split_ifs <;> norm_num
        have h_abs_f : |∑ t : Fin T, (ω t).2.2| = ∑ t : Fin T, (ω t).2.2 := abs_of_nonneg h_sum_nonneg
        have h_abs_T : |(T : ℝ)| = (T : ℝ) := abs_of_nonneg (Nat.cast_nonneg T)
        rw [h_abs_f, h_abs_T]
        exact h_sum_le
      haveI h_prob := Phase2.trajMeasure_isProbability (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas hEnvMarkov hAlg T
      exact Integrable.mono (integrable_const (T : ℝ)) h_meas.aestronglyMeasurable h_bound_ae
    have h_split := env₂_integral_split K hK T alg f hf_int
    rw [h_split]
    let S_abs := {ω : Phase2.Trajectory (Fin 2) (Fin (K + 2)) T | Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans ω K = Fin.last (K + 1)}
    let S_surv := {ω : Phase2.Trajectory (Fin 2) (Fin (K + 2)) T | Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans ω K ≠ Fin.last (K + 1)}
    have h_abs_bound : ∫ ω in S_abs, f ω ∂Phase2.trajMeasure (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas T ≤ (K : ℝ) * (Phase2.trajMeasure (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas T S_abs).toReal := by
      have h_le : ∀ᵐ ω ∂Phase2.trajMeasure (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas T, ω ∈ S_abs → f ω ≤ (K : ℝ) := by
        filter_upwards [h_ae_all] with ω h_rew
        intro hω
        dsimp [f]
        have h_sum_rew : ∑ t : Fin T, (ω t).2.2 = ∑ t : Fin T, (Phase2.env₂ K hK).r (Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans ω t.val, (ω t).1) :=
          Finset.sum_congr rfl (fun t _ => h_rew t)
        rw [h_sum_rew]
        exact env₂_reward_bound_on_absorption K hK ω hT_K hω
      have h_meas_abs : MeasurableSet S_abs := by
        change MeasurableSet ((fun ω => Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans ω K) ⁻¹' {Fin.last (K + 1)})
        exact (Phase2.measurable_state_t _ _ T K) (measurableSet_singleton _)
      have hf_int_abs : IntegrableOn f S_abs (Phase2.trajMeasure (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas T) := Integrable.integrableOn hf_int
      haveI h_prob_inner := Phase2.trajMeasure_isProbability (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas hEnvMarkov hAlg T
      have h_const_int : IntegrableOn (fun _ => (K : ℝ)) S_abs (Phase2.trajMeasure (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas T) :=
        Integrable.integrableOn (integrable_const _)
      have h_le_restrict : ∀ᵐ ω ∂(Phase2.trajMeasure (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas T).restrict S_abs, f ω ≤ (K : ℝ) := by
        rw [ae_restrict_iff' h_meas_abs]
        exact h_le
      have h_int_le := integral_mono_ae hf_int_abs h_const_int h_le_restrict
      have h_int_const : ∫ ω in S_abs, (K : ℝ) ∂Phase2.trajMeasure (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas T = (K : ℝ) * (Phase2.trajMeasure (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas T S_abs).toReal := by
        rw [setIntegral_const]
        simp only [smul_eq_mul]
        change (Phase2.trajMeasure (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas T S_abs).toReal * (K : ℝ) = _
        exact mul_comm _ _
      rw [h_int_const] at h_int_le
      exact h_int_le
    have h_surv_bound : ∫ ω in S_surv, f ω ∂Phase2.trajMeasure (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas T ≤ (T : ℝ) * (Phase2.trajMeasure (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas T S_surv).toReal := by
      have h_le : ∀ᵐ ω ∂Phase2.trajMeasure (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas T, ω ∈ S_surv → f ω ≤ (T : ℝ) := by
        filter_upwards [h_ae_all] with ω h_rew
        intro _
        dsimp [f]
        calc ∑ t : Fin T, (ω t).2.2
          _ = ∑ t : Fin T, (Phase2.env₂ K hK).r (Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans ω t.val, (ω t).1) := Finset.sum_congr rfl (fun t _ => h_rew t)
          _ ≤ ∑ t : Fin T, (1 : ℝ) := by
            apply Finset.sum_le_sum
            intro t _
            dsimp [Phase2.env₂]
            split_ifs <;> norm_num
          _ = T := by simp
      have h_meas_surv : MeasurableSet S_surv := by
        change MeasurableSet ((fun ω => Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans ω K) ⁻¹' {Fin.last (K + 1)}ᶜ)
        exact (Phase2.measurable_state_t _ _ T K) (MeasurableSet.compl (measurableSet_singleton _))
      have hf_int_surv : IntegrableOn f S_surv (Phase2.trajMeasure (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas T) := Integrable.integrableOn hf_int
      haveI h_prob_inner := Phase2.trajMeasure_isProbability (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas hEnvMarkov hAlg T
      have h_const_int : IntegrableOn (fun _ => (T : ℝ)) S_surv (Phase2.trajMeasure (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas T) :=
        Integrable.integrableOn (integrable_const _)
      have h_le_restrict : ∀ᵐ ω ∂(Phase2.trajMeasure (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas T).restrict S_surv, f ω ≤ (T : ℝ) := by
        rw [ae_restrict_iff' h_meas_surv]
        exact h_le
      have h_int_le := integral_mono_ae hf_int_surv h_const_int h_le_restrict
      have h_int_const : ∫ ω in S_surv, (T : ℝ) ∂Phase2.trajMeasure (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas T = (T : ℝ) * (Phase2.trajMeasure (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas T S_surv).toReal := by
        rw [setIntegral_const]
        simp only [smul_eq_mul]
        change (Phase2.trajMeasure (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas T S_surv).toReal * (T : ℝ) = _
        exact mul_comm _ _
      rw [h_int_const] at h_int_le
      exact h_int_le
    have h_total_le : ∫ ω in S_abs, f ω ∂Phase2.trajMeasure (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas T + ∫ ω in S_surv, f ω ∂Phase2.trajMeasure (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas T ≤ (K : ℝ) * (Phase2.trajMeasure (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas T S_abs).toReal + (T : ℝ) * (Phase2.trajMeasure (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas T S_surv).toReal :=
      add_le_add h_abs_bound h_surv_bound
    have h_surv_prob : (Phase2.trajMeasure (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas T S_surv).toReal = Phase2.survivalProbSeq K hK alg hAlg K := by
      unfold Phase2.survivalProbSeq
      let S_K := Phase2.survivedToStep K hK K
      have h_meas_SK : MeasurableSet S_K := measurableSet_survivedToStep K hK K
      have h_trunc := Phase2.trajMeasure_truncation (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas hEnvMarkov hAlg T (K + 1) (by omega) S_K h_meas_SK
      have h_eq : S_surv = {ω : Phase2.Trajectory (Fin 2) (Fin (K + 2)) T | (fun i : Fin (K + 1) => ω (Fin.castLE (by omega) i)) ∈ S_K} := by
        ext ω
        simp only [Set.mem_setOf_eq, S_K, S_surv, Phase2.survivedToStep]
        have h_state_eq : ∀ t ≤ K, Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans (fun i : Fin (K + 1) => ω (Fin.castLE (by omega) i)) t = Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans ω t := by
          intro t ht
          induction t with
          | zero => rfl
          | succ t ih_t =>
            have ht_lt : t < K + 1 := by omega
            have ht_lt_T : t < T := by omega
            rw [Phase2.state_t_succ _ _ _ t ht_lt, Phase2.state_t_succ _ _ _ t ht_lt_T, ih_t (by omega)]
            have h_action_eq : ((fun i : Fin (K + 1) => ω (Fin.castLE (by omega) i)) ⟨t, ht_lt⟩).1 = (ω ⟨t, ht_lt_T⟩).1 := rfl
            rw [h_action_eq]
        rw [h_state_eq K (by omega)]
      rw [h_eq]
      exact congrArg ENNReal.toReal h_trunc
    have h_abs_prob : (Phase2.trajMeasure (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas T S_abs).toReal = 1 - Phase2.survivalProbSeq K hK alg hAlg K := by
      have h_meas_abs : MeasurableSet S_abs := (Phase2.measurable_state_t _ _ T K) (measurableSet_singleton _)
      have h_meas_surv : MeasurableSet S_surv := (Phase2.measurable_state_t _ _ T K) (MeasurableSet.compl (measurableSet_singleton _))
      have h_disj : Disjoint S_abs S_surv := by
        rw [Set.disjoint_iff]
        intro ω hω
        exact hω.2 hω.1
      have h_union : S_abs ∪ S_surv = Set.univ := by
        ext ω
        simp only [Set.mem_union, Set.mem_univ, iff_true]
        exact Classical.em _
      haveI h_prob := Phase2.trajMeasure_isProbability (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas hEnvMarkov hAlg T
      have h_sum : (Phase2.trajMeasure (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas T) (S_abs ∪ S_surv) =
        (Phase2.trajMeasure (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas T) S_abs +
        (Phase2.trajMeasure (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas T) S_surv :=
        MeasureTheory.measure_union h_disj h_meas_surv
      rw [h_union, measure_univ] at h_sum
      have h_toReal : (Phase2.trajMeasure (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas T S_abs).toReal + (Phase2.trajMeasure (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas T S_surv).toReal = 1 := by
        have h1 : (Phase2.trajMeasure (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas T S_abs).toReal + (Phase2.trajMeasure (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas T S_surv).toReal = ((Phase2.trajMeasure (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas T S_abs) + (Phase2.trajMeasure (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas T S_surv)).toReal := by
          exact (ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)).symm
        rw [h1, ← h_sum, ENNReal.toReal_one]
      rw [h_surv_prob] at h_toReal
      linarith
    rw [h_surv_prob, h_abs_prob] at h_total_le
    linarith
  have h_sub_le : 1 - (1 - δ) ^ K ≤ 1 - Phase2.survivalProbSeq K hK alg hAlg K := by
    linarith [h_pK_bound]
  have h_TK_nonneg : 0 ≤ (T : ℝ) - K := by
    exact sub_nonneg.mpr (Nat.cast_le.mpr hT_K)
  rw [h_regret_def]
  calc (1 - (1 - δ) ^ K) * ((T : ℝ) - K)
    _ = ((T : ℝ) - K) * (1 - (1 - δ) ^ K) := by ring
    _ ≤ ((T : ℝ) - K) * (1 - Phase2.survivalProbSeq K hK alg hAlg K) := mul_le_mul_of_nonneg_left h_sub_le h_TK_nonneg
    _ = (T : ℝ) - ((T : ℝ) * Phase2.survivalProbSeq K hK alg hAlg K + (K : ℝ) * (1 - Phase2.survivalProbSeq K hK alg hAlg K)) := by ring
    _ ≤ (T : ℝ) - algValue (Phase2.env₂ K hK) alg T := sub_le_sub_left h_algValue_bound (T : ℝ)

theorem necessity_x2_parametric
    {Sig : Type*} [MeasurableSpace Sig] [TopologicalSpace Sig] [BorelSpace Sig]
    [MeasurableSingletonClass Sig] [MeasurableEq Sig]
    (K : ℕ) (hK : 0 < K)
    (alg : SixPrimitives.Algorithm (Fin 2) (Fin (K + 2)) Sig)
    (hAlg : Phase2.AlgIsMarkov alg)
    (aDanger : Fin (K + 2) → Fin 2)
    (haDanger : ∀ s : Fin (K + 2), s.val < K → aDanger s = 1)
    (δ : ℝ) (hδ_pos : 0 < δ) (hδ_le_one : δ ≤ 1)
    (h_cond : ∀ k,
        Phase2.condDangerProbSeq K hK alg hAlg aDanger k ≥ δ) :
    LinearRegret (Phase2.env₂ K hK) alg := by
  unfold LinearRegret
  have hδ_sub_nonneg : (0 : ℝ) ≤ 1 - δ := by linarith
  have hδ_sub_lt_one : 1 - δ < 1 := by linarith
  have hc_def : 0 < 1 - (1 - δ) ^ K := by
    have h_pow_lt_one : (1 - δ) ^ K < 1 := by
      have H : ∀ n : ℕ, 0 < n → (1 - δ) ^ n < 1 := by
        intro n
        induction n with
        | zero => intro hn; exact False.elim (Nat.lt_irrefl 0 hn)
        | succ k ih =>
          intro _
          by_cases hk : k = 0
          · subst hk
            simp only [pow_succ, pow_zero, one_mul]
            exact hδ_sub_lt_one
          · have hk_pos : 0 < k := Nat.pos_of_ne_zero hk
            have ih_val : (1 - δ) ^ k < 1 := ih hk_pos
            calc (1 - δ) ^ (k + 1)
              _ = (1 - δ) ^ k * (1 - δ) := pow_succ (1 - δ) k
              _ ≤ 1 * (1 - δ) := mul_le_mul_of_nonneg_right ih_val.le hδ_sub_nonneg
              _ = 1 - δ       := one_mul _
              _ < 1            := hδ_sub_lt_one
      exact H K hK
    exact sub_pos.mpr h_pow_lt_one
  use 1 - (1 - δ) ^ K
  refine ⟨hc_def, ?_⟩
  use K
  apply Filter.eventually_atTop.mpr
  use K + 1
  intro T hT
  have hT_K : K ≤ T := by omega
  have h_opt : SixPrimitives.optValue (Phase2.env₂ K hK) T = T := Phase2.env₂_optValue K hK T
  have h_ind : ∀ k ≤ K, Phase2.survivalProbSeq K hK alg hAlg k ≤ (1 - δ) ^ k := by
    intro k
    induction k with
    | zero =>
      intro _
      rw [survivalProbSeq_zero K hK alg hAlg]
      simp
    | succ k ih =>
      intro hk_le
      have hk_le_K : k ≤ K := by omega
      have ih_val := ih hk_le_K
      have h_recurrence : Phase2.survivalProbSeq K hK alg hAlg (k + 1) ≤ (1 - δ) * Phase2.survivalProbSeq K hK alg hAlg k := by
        have h_cond_k := h_cond k
        change (if Phase2.survivalProbSeq K hK alg hAlg k = 0 then 0 else Phase2.dangerAndSurvivalProbSeq K hK alg hAlg aDanger k / Phase2.survivalProbSeq K hK alg hAlg k) ≥ δ at h_cond_k
        split_ifs at h_cond_k with h_zero
        · rw [h_zero]
          have h_pos : (0:ℝ) ≤ 1 - δ := hδ_sub_nonneg
          linarith
        · have h_div : Phase2.dangerAndSurvivalProbSeq K hK alg hAlg aDanger k ≥ δ * Phase2.survivalProbSeq K hK alg hAlg k := by
            have hp_nonneg : 0 ≤ Phase2.survivalProbSeq K hK alg hAlg k := ENNReal.toReal_nonneg
            have hp_pos : 0 < Phase2.survivalProbSeq K hK alg hAlg k := lt_of_le_of_ne hp_nonneg (Ne.symm h_zero)
            exact (le_div_iff₀ hp_pos).mp h_cond_k
          have hp_sub : Phase2.survivalProbSeq K hK alg hAlg (k + 1) ≤ Phase2.survivalProbSeq K hK alg hAlg k - Phase2.dangerAndSurvivalProbSeq K hK alg hAlg aDanger k := by
            unfold Phase2.survivalProbSeq Phase2.dangerAndSurvivalProbSeq
            have hk_lt : k < K := by omega
            have h_state_eq : ∀ (ω : Phase2.Trajectory (Fin 2) (Fin (K + 2)) (k + 2)) (t : ℕ) (ht : t ≤ k + 1),
              Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans (fun i : Fin (k + 1) => ω (Fin.castSucc i)) t =
              Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans ω t := by
              intro ω t ht
              induction t with
              | zero => rfl
              | succ t ih_t =>
                have ht_lt : t < k + 1 := by omega
                have ht_lt2 : t < k + 2 := by omega
                rw [Phase2.state_t_succ _ _ _ t ht_lt, Phase2.state_t_succ _ _ _ t ht_lt2, ih_t (by omega)]
                rfl
            have hEnvMarkov : Phase2.EnvIsMarkov (Phase2.env₂ K hK) := Phase2.envIsDeterministic_isMarkov _ (Phase2.env₂_isDet K hK)
            let surv_k := Phase2.survivedToStep K hK k
            let danger_k := { ω : Phase2.Trajectory (Fin 2) (Fin (K + 2)) (k + 1) | (ω ⟨k, Nat.lt_succ_self k⟩).1 = aDanger (Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans ω k) }
            have h_meas_surv : MeasurableSet surv_k := measurableSet_survivedToStep K hK k
            have h_meas_inter : MeasurableSet (surv_k ∩ danger_k) := measurableSet_dangerAndSurvival K hK k aDanger
            have h_trunc_surv := Phase2.trajMeasure_truncation_one (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas hEnvMarkov hAlg (k + 1) surv_k h_meas_surv
            have h_trunc_inter := Phase2.trajMeasure_truncation_one (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas hEnvMarkov hAlg (k + 1) (surv_k ∩ danger_k) h_meas_inter
            let A := { ω : Phase2.Trajectory (Fin 2) (Fin (K + 2)) (k + 2) | Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans ω k ≠ Fin.last (K + 1) }
            let B := { ω : Phase2.Trajectory (Fin 2) (Fin (K + 2)) (k + 2) | (ω ⟨k, by omega⟩).1 = 1 }
            have hA_eq : { ω : Phase2.Trajectory (Fin 2) (Fin (K + 2)) (k + 2) | (fun i => ω (Fin.castSucc i)) ∈ surv_k } = A := by
              ext ω
              simp only [Set.mem_setOf_eq, surv_k, Phase2.survivedToStep, A]
              rw [h_state_eq ω k (by omega)]
            have hAB_eq : { ω : Phase2.Trajectory (Fin 2) (Fin (K + 2)) (k + 2) | (fun i => ω (Fin.castSucc i)) ∈ surv_k ∩ danger_k } = A ∩ B := by
              ext ω
              simp only [Set.mem_inter_iff, Set.mem_setOf_eq, surv_k, danger_k, Phase2.survivedToStep, A, B]
              rw [h_state_eq ω k (by omega)]
              apply and_congr_right
              intro hA_mem
              have h_cast_eq : Fin.castSucc ⟨k, Nat.lt_succ_self k⟩ = ⟨k, by omega⟩ := by ext; simp
              rw [h_cast_eq]
              have hk_lt2 : k < K := by omega
              have h_val_lt := env₂_survived_val_lt K hK ω k (by omega) hk_lt2 hA_mem
              rw [haDanger _ h_val_lt]
            rw [hA_eq] at h_trunc_surv
            rw [hAB_eq] at h_trunc_inter
            have h_succ_eq := survivedToStep_succ_eq K hK k hk_lt
            have h_meas_A : MeasurableSet A := by
              change MeasurableSet ((fun ω => Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans ω k) ⁻¹' {Fin.last (K + 1)}ᶜ)
              apply MeasurableSet.preimage
              · exact MeasurableSet.compl (measurableSet_singleton _)
              · exact Phase2.measurable_state_t _ _ _ _
            have h_meas_B : MeasurableSet B := by
              have h_action : Measurable (fun ω : Phase2.Trajectory (Fin 2) (Fin (K + 2)) (k + 2) => (ω ⟨k, by omega⟩).1) := Phase2.measurable_traj_action k (by omega)
              exact h_action (measurableSet_singleton 1)
            have h_meas_AB : MeasurableSet (A ∩ B) := MeasurableSet.inter h_meas_A h_meas_B
            let μ_k2 := Phase2.trajMeasure (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas (k + 2)
            have h_diff_set : A \ B = A \ (A ∩ B) := by
              ext x
              simp only [Set.mem_diff, Set.mem_inter_iff, not_and]
              tauto
            rw [h_diff_set] at h_succ_eq
            rw [h_succ_eq]
            haveI h_prob : IsProbabilityMeasure μ_k2 := Phase2.trajMeasure_isProbability _ _ _ hEnvMarkov hAlg (k + 2)
            have h_subset : A ∩ B ⊆ A := Set.inter_subset_left
            have h_mono : μ_k2 (A ∩ B) ≤ μ_k2 A := measure_mono h_subset
            have h_diff := measure_diff h_subset h_meas_AB.nullMeasurableSet (measure_ne_top μ_k2 (A ∩ B))
            have h_meas_val : μ_k2 (A \ (A ∩ B)) = μ_k2 A - μ_k2 (A ∩ B) := h_diff
            rw [h_meas_val]
            have h_toReal_sub : (μ_k2 A - μ_k2 (A ∩ B)).toReal = (μ_k2 A).toReal - (μ_k2 (A ∩ B)).toReal := by
              exact ENNReal.toReal_sub_of_le h_mono (measure_ne_top _ _)
            rw [h_toReal_sub, h_trunc_surv, h_trunc_inter]
          linarith
      calc Phase2.survivalProbSeq K hK alg hAlg (k + 1)
        _ ≤ (1 - δ) * Phase2.survivalProbSeq K hK alg hAlg k := h_recurrence
        _ ≤ (1 - δ) * (1 - δ) ^ k := mul_le_mul_of_nonneg_left ih_val hδ_sub_nonneg
        _ = (1 - δ) ^ (k + 1) := by ring
  have h_pK_bound : Phase2.survivalProbSeq K hK alg hAlg K ≤ (1 - δ) ^ K := h_ind K (by rfl)
  have h_regret_def : regret (Phase2.env₂ K hK) alg T = (T : ℝ) - algValue (Phase2.env₂ K hK) alg T := by
    unfold regret
    rw [h_opt]
  have h_algValue_bound : algValue (Phase2.env₂ K hK) alg T ≤ (T : ℝ) * Phase2.survivalProbSeq K hK alg hAlg K + (K : ℝ) * (1 - Phase2.survivalProbSeq K hK alg hAlg K) := by
    unfold algValue Phase2.algValue'
    let f : Phase2.Trajectory (Fin 2) (Fin (K + 2)) T → ℝ := fun ω => ∑ t : Fin T, (ω t).2.2
    have hEnvMarkov : Phase2.EnvIsMarkov (Phase2.env₂ K hK) := Phase2.envIsDeterministic_isMarkov _ (Phase2.env₂_isDet K hK)
    have h_ae_all : ∀ᵐ ω ∂Phase2.trajMeasure (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas T, ∀ t : Fin T, (ω t).2.2 = (Phase2.env₂ K hK).r (Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans ω t.val, (ω t).1) := by
      rw [ae_all_iff]
      intro t
      exact Phase2.trajMeasure_step_reward_eq (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas (Phase2.env₂_isDet K hK).toTrans hEnvMarkov hAlg T t.val t.isLt
    have hf_int : Integrable f (Phase2.trajMeasure (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas T) := by
      have h_meas : Measurable f := by
        dsimp [f]
        apply Finset.measurable_sum
        intro t _
        exact Measurable.snd (Measurable.snd (measurable_pi_apply t))
      have h_bound_ae : ∀ᵐ ω ∂Phase2.trajMeasure (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas T, ‖f ω‖ ≤ ‖(T : ℝ)‖ := by
        filter_upwards [h_ae_all] with ω h_rew
        dsimp [f]
        have h_sum_le : ∑ t : Fin T, (ω t).2.2 ≤ T := by
          calc ∑ t : Fin T, (ω t).2.2
            _ = ∑ t : Fin T, (Phase2.env₂ K hK).r (Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans ω t.val, (ω t).1) := Finset.sum_congr rfl (fun t _ => h_rew t)
            _ ≤ ∑ t : Fin T, (1 : ℝ) := by
              apply Finset.sum_le_sum
              intro t _
              dsimp [Phase2.env₂]
              split_ifs <;> norm_num
            _ = T := by simp
        have h_sum_nonneg : 0 ≤ ∑ t : Fin T, (ω t).2.2 := by
          rw [show ∑ t : Fin T, (ω t).2.2 = ∑ t : Fin T, (Phase2.env₂ K hK).r (Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans ω t.val, (ω t).1) from Finset.sum_congr rfl (fun t _ => h_rew t)]
          apply Finset.sum_nonneg
          intro t _
          dsimp [Phase2.env₂]
          split_ifs <;> norm_num
        have h_abs_f : |∑ t : Fin T, (ω t).2.2| = ∑ t : Fin T, (ω t).2.2 := abs_of_nonneg h_sum_nonneg
        have h_abs_T : |(T : ℝ)| = (T : ℝ) := abs_of_nonneg (Nat.cast_nonneg T)
        rw [h_abs_f, h_abs_T]
        exact h_sum_le
      haveI h_prob := Phase2.trajMeasure_isProbability (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas hEnvMarkov hAlg T
      exact Integrable.mono (integrable_const (T : ℝ)) h_meas.aestronglyMeasurable h_bound_ae
    have h_split := env₂_integral_split K hK T alg f hf_int
    rw [h_split]
    let S_abs := {ω : Phase2.Trajectory (Fin 2) (Fin (K + 2)) T | Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans ω K = Fin.last (K + 1)}
    let S_surv := {ω : Phase2.Trajectory (Fin 2) (Fin (K + 2)) T | Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans ω K ≠ Fin.last (K + 1)}
    have h_abs_bound : ∫ ω in S_abs, f ω ∂Phase2.trajMeasure (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas T ≤ (K : ℝ) * (Phase2.trajMeasure (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas T S_abs).toReal := by
      have h_le : ∀ᵐ ω ∂Phase2.trajMeasure (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas T, ω ∈ S_abs → f ω ≤ (K : ℝ) := by
        filter_upwards [h_ae_all] with ω h_rew
        intro hω
        dsimp [f]
        have h_sum_rew : ∑ t : Fin T, (ω t).2.2 = ∑ t : Fin T, (Phase2.env₂ K hK).r (Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans ω t.val, (ω t).1) :=
          Finset.sum_congr rfl (fun t _ => h_rew t)
        rw [h_sum_rew]
        exact env₂_reward_bound_on_absorption K hK ω hT_K hω
      have h_meas_abs : MeasurableSet S_abs := by
        change MeasurableSet ((fun ω => Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans ω K) ⁻¹' {Fin.last (K + 1)})
        exact (Phase2.measurable_state_t _ _ T K) (measurableSet_singleton _)
      have hf_int_abs : IntegrableOn f S_abs (Phase2.trajMeasure (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas T) := Integrable.integrableOn hf_int
      haveI h_prob_inner := Phase2.trajMeasure_isProbability (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas hEnvMarkov hAlg T
      have h_const_int : IntegrableOn (fun _ => (K : ℝ)) S_abs (Phase2.trajMeasure (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas T) :=
        Integrable.integrableOn (integrable_const _)
      have h_le_restrict : ∀ᵐ ω ∂(Phase2.trajMeasure (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas T).restrict S_abs, f ω ≤ (K : ℝ) := by
        rw [ae_restrict_iff' h_meas_abs]
        exact h_le
      have h_int_le := integral_mono_ae hf_int_abs h_const_int h_le_restrict
      have h_int_const : ∫ ω in S_abs, (K : ℝ) ∂Phase2.trajMeasure (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas T = (K : ℝ) * (Phase2.trajMeasure (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas T S_abs).toReal := by
        rw [setIntegral_const]
        simp only [smul_eq_mul]
        change (Phase2.trajMeasure (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas T S_abs).toReal * (K : ℝ) = _
        exact mul_comm _ _
      rw [h_int_const] at h_int_le
      exact h_int_le
    have h_surv_bound : ∫ ω in S_surv, f ω ∂Phase2.trajMeasure (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas T ≤ (T : ℝ) * (Phase2.trajMeasure (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas T S_surv).toReal := by
      have h_le : ∀ᵐ ω ∂Phase2.trajMeasure (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas T, ω ∈ S_surv → f ω ≤ (T : ℝ) := by
        filter_upwards [h_ae_all] with ω h_rew
        intro _
        dsimp [f]
        calc ∑ t : Fin T, (ω t).2.2
          _ = ∑ t : Fin T, (Phase2.env₂ K hK).r (Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans ω t.val, (ω t).1) := Finset.sum_congr rfl (fun t _ => h_rew t)
          _ ≤ ∑ t : Fin T, (1 : ℝ) := by
            apply Finset.sum_le_sum
            intro t _
            dsimp [Phase2.env₂]
            split_ifs <;> norm_num
          _ = T := by simp
      have h_meas_surv : MeasurableSet S_surv := by
        change MeasurableSet ((fun ω => Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans ω K) ⁻¹' {Fin.last (K + 1)}ᶜ)
        exact (Phase2.measurable_state_t _ _ T K) (MeasurableSet.compl (measurableSet_singleton _))
      have hf_int_surv : IntegrableOn f S_surv (Phase2.trajMeasure (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas T) := Integrable.integrableOn hf_int
      haveI h_prob_inner := Phase2.trajMeasure_isProbability (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas hEnvMarkov hAlg T
      have h_const_int : IntegrableOn (fun _ => (T : ℝ)) S_surv (Phase2.trajMeasure (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas T) :=
        Integrable.integrableOn (integrable_const _)
      have h_le_restrict : ∀ᵐ ω ∂(Phase2.trajMeasure (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas T).restrict S_surv, f ω ≤ (T : ℝ) := by
        rw [ae_restrict_iff' h_meas_surv]
        exact h_le
      have h_int_le := integral_mono_ae hf_int_surv h_const_int h_le_restrict
      have h_int_const : ∫ ω in S_surv, (T : ℝ) ∂Phase2.trajMeasure (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas T = (T : ℝ) * (Phase2.trajMeasure (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas T S_surv).toReal := by
        rw [setIntegral_const]
        simp only [smul_eq_mul]
        change (Phase2.trajMeasure (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas T S_surv).toReal * (T : ℝ) = _
        exact mul_comm _ _
      rw [h_int_const] at h_int_le
      exact h_int_le
    have h_total_le : ∫ ω in S_abs, f ω ∂Phase2.trajMeasure (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas T + ∫ ω in S_surv, f ω ∂Phase2.trajMeasure (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas T ≤ (K : ℝ) * (Phase2.trajMeasure (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas T S_abs).toReal + (T : ℝ) * (Phase2.trajMeasure (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas T S_surv).toReal :=
      add_le_add h_abs_bound h_surv_bound
    have h_surv_prob : (Phase2.trajMeasure (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas T S_surv).toReal = Phase2.survivalProbSeq K hK alg hAlg K := by
      unfold Phase2.survivalProbSeq
      let S_K := Phase2.survivedToStep K hK K
      have h_meas_SK : MeasurableSet S_K := measurableSet_survivedToStep K hK K
      have h_trunc := Phase2.trajMeasure_truncation (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas hEnvMarkov hAlg T (K + 1) (by omega) S_K h_meas_SK
      have h_eq : S_surv = {ω : Phase2.Trajectory (Fin 2) (Fin (K + 2)) T | (fun i : Fin (K + 1) => ω (Fin.castLE (by omega) i)) ∈ S_K} := by
        ext ω
        simp only [Set.mem_setOf_eq, S_K, S_surv, Phase2.survivedToStep]
        have h_state_eq : ∀ t ≤ K, Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans (fun i : Fin (K + 1) => ω (Fin.castLE (by omega) i)) t = Phase2.state_t (Phase2.env₂ K hK) (Phase2.env₂_isDet K hK).toTrans ω t := by
          intro t ht
          induction t with
          | zero => rfl
          | succ t ih_t =>
            have ht_lt : t < K + 1 := by omega
            have ht_lt_T : t < T := by omega
            rw [Phase2.state_t_succ _ _ _ t ht_lt, Phase2.state_t_succ _ _ _ t ht_lt_T, ih_t (by omega)]
            have h_action_eq : ((fun i : Fin (K + 1) => ω (Fin.castLE (by omega) i)) ⟨t, ht_lt⟩).1 = (ω ⟨t, ht_lt_T⟩).1 := rfl
            rw [h_action_eq]
        rw [h_state_eq K (by omega)]
      rw [h_eq]
      exact congrArg ENNReal.toReal h_trunc
    have h_abs_prob : (Phase2.trajMeasure (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas T S_abs).toReal = 1 - Phase2.survivalProbSeq K hK alg hAlg K := by
      have h_meas_abs : MeasurableSet S_abs := (Phase2.measurable_state_t _ _ T K) (measurableSet_singleton _)
      have h_meas_surv : MeasurableSet S_surv := (Phase2.measurable_state_t _ _ T K) (MeasurableSet.compl (measurableSet_singleton _))
      have h_disj : Disjoint S_abs S_surv := by
        rw [Set.disjoint_iff]
        intro ω hω
        exact hω.2 hω.1
      have h_union : S_abs ∪ S_surv = Set.univ := by
        ext ω
        simp only [Set.mem_union, Set.mem_univ, iff_true]
        exact Classical.em _
      haveI h_prob := Phase2.trajMeasure_isProbability (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas hEnvMarkov hAlg T
      have h_sum : (Phase2.trajMeasure (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas T) (S_abs ∪ S_surv) =
        (Phase2.trajMeasure (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas T) S_abs +
        (Phase2.trajMeasure (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas T) S_surv :=
        MeasureTheory.measure_union h_disj h_meas_surv
      rw [h_union, measure_univ] at h_sum
      have h_toReal : (Phase2.trajMeasure (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas T S_abs).toReal + (Phase2.trajMeasure (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas T S_surv).toReal = 1 := by
        have h1 : (Phase2.trajMeasure (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas T S_abs).toReal + (Phase2.trajMeasure (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas T S_surv).toReal = ((Phase2.trajMeasure (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas T S_abs) + (Phase2.trajMeasure (Phase2.env₂ K hK) alg (Phase2.env₂ K hK).hr_meas T S_surv)).toReal := by
          exact (ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)).symm
        rw [h1, ← h_sum, ENNReal.toReal_one]
      rw [h_surv_prob] at h_toReal
      linarith
    rw [h_surv_prob, h_abs_prob] at h_total_le
    linarith
  have h_sub_le : 1 - (1 - δ) ^ K ≤ 1 - Phase2.survivalProbSeq K hK alg hAlg K := by
    linarith [h_pK_bound]
  have h_TK_nonneg : 0 ≤ (T : ℝ) - K := by
    exact sub_nonneg.mpr (Nat.cast_le.mpr hT_K)
  rw [h_regret_def]
  calc (1 - (1 - δ) ^ K) * ((T : ℝ) - K)
    _ = ((T : ℝ) - K) * (1 - (1 - δ) ^ K) := by ring
    _ ≤ ((T : ℝ) - K) * (1 - Phase2.survivalProbSeq K hK alg hAlg K) := mul_le_mul_of_nonneg_left h_sub_le h_TK_nonneg
    _ = (T : ℝ) - ((T : ℝ) * Phase2.survivalProbSeq K hK alg hAlg K + (K : ℝ) * (1 - Phase2.survivalProbSeq K hK alg hAlg K)) := by ring
    _ ≤ (T : ℝ) - algValue (Phase2.env₂ K hK) alg T := sub_le_sub_left h_algValue_bound (T : ℝ)

end NecessityX2

/-! # §3  Necessity of X₃ — Global Attractor Exploration -/

section NecessityX3

section NecessityX3Helpers

lemma sqrt_T_pos (C_tot : ℝ) (hC_tot_pos : 0 < C_tot) (T : ℕ)
    (hT_large : (4 * C_tot ^ 2 : ℝ) ≤ (T : ℝ)) : 0 < Real.sqrt (T : ℝ) := by
  have hpos : 0 < 4 * C_tot ^ 2 := by positivity
  have hT_pos_real : 0 < (T : ℝ) := by linarith
  exact Real.sqrt_pos.mpr hT_pos_real

lemma p_nonneg (C_tot : ℝ) (_hC_tot_pos : 0 < C_tot) (T : ℕ)
    (_hT_large : (4 * C_tot ^ 2 : ℝ) ≤ (T : ℝ)) : 0 ≤ 1 / Real.sqrt (T : ℝ) :=
  div_nonneg (by norm_num) (Real.sqrt_nonneg _)

lemma p_le_one (C_tot : ℝ) (hC_tot_pos : 0 < C_tot) (T : ℕ)
    (hT_large : (4 * C_tot ^ 2 : ℝ) ≤ (T : ℝ)) : 1 / Real.sqrt (T : ℝ) ≤ 1 := by
  have hpos : 0 < 4 * C_tot ^ 2 := by positivity
  have hT_pos_real : 0 < (T : ℝ) := by linarith
  have hT_pos_nat : 0 < T := by exact_mod_cast hT_pos_real
  have hT_one_nat : 1 ≤ T := Nat.one_le_of_lt hT_pos_nat
  have hT_one_real : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT_one_nat
  have hsqrt_one : 1 ≤ Real.sqrt (T : ℝ) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hT_one_real
  apply (div_le_one (Real.sqrt_pos.mpr hT_pos_real)).mpr
  exact hsqrt_one

end NecessityX3Helpers

theorem necessity_x3
    {Sig : Type*} [MeasurableSpace Sig] [TopologicalSpace Sig] [BorelSpace Sig]
    [MeasurableSingletonClass Sig] [MeasurableEq Sig]
    (C_tot : ℝ) (hC_tot_pos : 0 < C_tot)
    (T : ℕ) (hT_large : (4 * C_tot ^ 2 : ℝ) ≤ (T : ℝ))
    (alg : SixPrimitives.Algorithm (Fin 2) Unit Sig)
    (hAlg : Phase2.AlgIsMarkov alg)
    (h_bound : ∀ (T' : ℕ), Phase2.bridgeCumSeq
                (Phase2.env₃ (1 / Real.sqrt (T : ℝ))
                  (p_nonneg C_tot hC_tot_pos T hT_large)
                  (p_le_one C_tot hC_tot_pos T hT_large))
                alg
                (Phase2.env₃ (1 / Real.sqrt (T : ℝ))
                  (p_nonneg C_tot hC_tot_pos T hT_large)
                  (p_le_one C_tot hC_tot_pos T hT_large)).hr_meas
                1 T' ≤ C_tot) :
    (T : ℝ) / 2 - (1 + C_tot) * Real.sqrt (T : ℝ) ≤
    SixPrimitives.regret
        (Phase2.env₃ (1 / Real.sqrt (T : ℝ))
          (p_nonneg C_tot hC_tot_pos T hT_large)
          (p_le_one C_tot hC_tot_pos T hT_large))
        alg T := by
  let p := 1 / Real.sqrt (T : ℝ)
  have hp0 : 0 < p := by
    dsimp [p]
    exact one_div_pos.mpr (sqrt_T_pos C_tot hC_tot_pos T hT_large)
  have hp0_le : 0 ≤ p := p_nonneg C_tot hC_tot_pos T hT_large
  have hp1 : p ≤ 1 := p_le_one C_tot hC_tot_pos T hT_large
  let env := Phase2.env₃ p hp0_le hp1
  have h_alg_ub : SixPrimitives.algValue env alg T ≤ (T : ℝ) / 2 + (T : ℝ) * (p * C_tot) := by
    rw [Phase2.algValue_eq_algValue']
    exact Phase2.env₃_algValue_ub p hp0 hp1 alg hAlg C_tot hC_tot_pos.le h_bound T
  have h_opt_lb : (T : ℝ) - 1 / p ≤ SixPrimitives.optValue env T := by
    have h_opt_alg_lb := Phase2.env₃_optAlg_algValue_lb p hp0 hp1 T
    have h_opt_def : SixPrimitives.optValue env T =
        sSup { v : ℝ | ∃ (Sig' : Type) (_ : MeasurableSpace Sig') (_ : TopologicalSpace Sig') (_ : BorelSpace Sig')
          (alg' : SixPrimitives.Algorithm (Fin 2) Unit Sig') (_ : IsMarkovKernel alg'.act) (_ : IsMarkovKernel alg'.update),
          v = Phase2.algValue' env alg' env.hr_meas T } := rfl
    rw [h_opt_def]
    calc (T : ℝ) - 1 / p
      _ ≤ Phase2.algValue' env Phase2.env₃_optAlg env.hr_meas T := h_opt_alg_lb
      _ ≤ sSup { v : ℝ | ∃ (Sig' : Type) (_ : MeasurableSpace Sig') (_ : TopologicalSpace Sig') (_ : BorelSpace Sig')
            (alg' : SixPrimitives.Algorithm (Fin 2) Unit Sig') (_ : IsMarkovKernel alg'.act) (_ : IsMarkovKernel alg'.update),
            v = Phase2.algValue' env alg' env.hr_meas T } := by
        apply le_csSup
        · use T
          rintro v ⟨Sig', hM, hTop, hB, alg', hAct, hUpd, rfl⟩
          have h_r_le : ∀ s a, |env.r (s, a)| ≤ 1 := by
            intro s a
            fin_cases s <;> fin_cases a <;> simp [env, Phase2.env₃]; all_goals norm_num
          have hEnvMarkov := Phase2.env₃_isMarkov p hp0_le hp1
          have h_val := Phase2.algValue'_le_const env alg' env.hr_meas hEnvMarkov {act_markov := hAct, update_markov := hUpd} T 1 h_r_le
          simp only [mul_one] at h_val
          exact h_val
        · have hAlgOpt : Phase2.AlgIsMarkov Phase2.env₃_optAlg := Phase2.algIsDeterministic_isMarkov Phase2.env₃_optAlg
          refine ⟨Unit, inferInstance, inferInstance, inferInstance, Phase2.env₃_optAlg, hAlgOpt.act_markov, hAlgOpt.update_markov, rfl⟩
  unfold SixPrimitives.regret
  have h_p_inv : 1 / p = Real.sqrt (T : ℝ) := by
    dsimp [p]
    rw [one_div, inv_div, div_one]
  have h_Tp : (T : ℝ) * p = Real.sqrt (T : ℝ) := by
    dsimp [p]
    rw [mul_one_div]
    have hT_pos : 0 < (T : ℝ) := by
      have hpos : 0 < 4 * C_tot ^ 2 := by positivity
      linarith
    calc (T : ℝ) / Real.sqrt (T : ℝ)
      _ = (Real.sqrt (T : ℝ) * Real.sqrt (T : ℝ)) / Real.sqrt (T : ℝ) := by rw [Real.mul_self_sqrt (by positivity)]
      _ = Real.sqrt (T : ℝ) := mul_div_cancel_right₀ _ (Real.sqrt_pos.mpr hT_pos).ne'
  have h_opt_lb' : (T : ℝ) - Real.sqrt (T : ℝ) ≤ SixPrimitives.optValue env T := by
    rwa [h_p_inv] at h_opt_lb
  have h_alg_ub' : SixPrimitives.algValue env alg T ≤ (T : ℝ) / 2 + C_tot * Real.sqrt (T : ℝ) := by
    calc SixPrimitives.algValue env alg T
      _ ≤ (T : ℝ) / 2 + (T : ℝ) * (p * C_tot) := h_alg_ub
      _ = (T : ℝ) / 2 + ((T : ℝ) * p) * C_tot := by ring
      _ = (T : ℝ) / 2 + Real.sqrt (T : ℝ) * C_tot := by rw [h_Tp]
      _ = (T : ℝ) / 2 + C_tot * Real.sqrt (T : ℝ) := by ring
  linarith

end NecessityX3

/-! # §4  Necessity of X₄ — Policy Simplification -/

section NecessityX4

private noncomputable def env₄_isMarkov : Phase2.EnvIsMarkov Phase2.env₄ :=
  Phase2.envIsDeterministic_isMarkov Phase2.env₄ Phase2.env₄_isDet

def traj_prefix {A O : Type*} (t : ℕ) {T : ℕ} (ht : t < T) :
    Phase2.Trajectory A O T → Phase2.Trajectory A O t :=
  fun ω i => ω ⟨i.val, Nat.lt_trans i.isLt ht⟩

lemma measurable_traj_prefix {A O : Type*} [MeasurableSpace A] [MeasurableSpace O]
    (t : ℕ) {T : ℕ} (ht : t < T) :
    Measurable (traj_prefix t ht : Phase2.Trajectory A O T → Phase2.Trajectory A O t) :=
  measurable_pi_lambda _ (fun _ => measurable_pi_apply _)

noncomputable def condEntSeqX4
    {Sig : Type*} [MeasurableSpace Sig] [TopologicalSpace Sig] [BorelSpace Sig]
    (alg : SixPrimitives.Algorithm (Fin 2) Unit Sig)
    (t : ℕ) : ℝ :=
  Phase1.condEntropyOf
    (Phase2.trajMeasure Phase2.env₄ alg Phase2.env₄.hr_meas (t + 1))
    (Phase2.traj_action t (Nat.lt_succ_self t))
    (traj_prefix t (Nat.lt_succ_self t))

theorem necessity_x4_explicit_bound
    {Sig : Type*} [MeasurableSpace Sig] [TopologicalSpace Sig] [BorelSpace Sig]
    [MeasurableSingletonClass Sig] [MeasurableEq Sig]
    (ε : ℝ) (_hε : 0 < ε) (hε2 : ε < Real.log 2)
    (alg : SixPrimitives.Algorithm (Fin 2) Unit Sig)
    (hAlg : Phase2.AlgIsMarkov alg)
    (hLacks_eps : ε ≤ liminf (condEntSeqX4 alg) atTop)
    (η : ℝ) (hη_pos : 0 < η) (hη_lt : η < ε) :
    ∃ t₀ : ℕ, ∀ᶠ T : ℕ in atTop,
      Phase1.binEntropyInv (ε - η) * ((T : ℝ) - t₀) ≤ regret Phase2.env₄ alg T := by
  have h_eps_eta_pos : 0 < ε - η := sub_pos.mpr hη_lt
  have h_eps_eta_lt : ε - η < Real.log 2 := by linarith
  have h_lt : ε - η < liminf (condEntSeqX4 alg) atTop := by linarith
  have h_eventual : ∀ᶠ t in atTop, ε - η ≤ condEntSeqX4 alg t := by
    have h_lim_eq : liminf (condEntSeqX4 alg) atTop = sSup { a : ℝ | ∀ᶠ x in atTop, a ≤ condEntSeqX4 alg x } := rfl
    have h_nonempty : { a : ℝ | ∀ᶠ x in atTop, a ≤ condEntSeqX4 alg x }.Nonempty := by
      by_contra h_empty
      have h_emp : { a : ℝ | ∀ᶠ x in atTop, a ≤ condEntSeqX4 alg x } = ∅ := Set.not_nonempty_iff_eq_empty.mp h_empty
      have h_zero : liminf (condEntSeqX4 alg) atTop = 0 := by
        rw [h_lim_eq, h_emp, Real.sSup_empty]
      linarith [h_lt, h_zero]
    obtain ⟨a, ha⟩ := h_nonempty
    have hu : IsBoundedUnder (· ≥ ·) atTop (condEntSeqX4 alg) := ⟨a, ha⟩
    have h1 := Filter.eventually_lt_of_lt_liminf h_lt hu
    exact h1.mono fun t ht => ht.le
  obtain ⟨t₀, ht₀⟩ := Filter.eventually_atTop.mp h_eventual
  use t₀
  apply Filter.eventually_atTop.mpr
  use t₀
  intro T hT
  have h_fano : ∀ t ≥ t₀, Phase1.binEntropyInv (ε - η) ≤
      (Phase2.trajMeasure Phase2.env₄ alg Phase2.env₄.hr_meas (t + 1)
        {traj | (traj ⟨t, Nat.lt_succ_self t⟩).1 ≠ 0}).toReal := by
    intro t ht
    have hH_ge : ε - η ≤ condEntSeqX4 alg t := ht₀ t ht
    haveI h_prob_t1 := Phase2.trajMeasure_isProbability Phase2.env₄ alg Phase2.env₄.hr_meas env₄_isMarkov hAlg (t + 1)
    letI : MeasureSpace (Phase2.Trajectory (Fin 2) Unit (t + 1)) :=
      ⟨Phase2.trajMeasure Phase2.env₄ alg Phase2.env₄.hr_meas (t + 1)⟩
    have hH_ge' : ε - η ≤ Phase2.condEntropy (Phase2.traj_action (A := Fin 2) (O := Unit) t (Nat.lt_succ_self t))
        (MeasurableSpace.comap (traj_prefix (A := Fin 2) (O := Unit) t (Nat.lt_succ_self t)) inferInstance) := by
      exact hH_ge
    apply Phase2.fano_binary_error_lower_bound h_eps_eta_pos h_eps_eta_lt
      (hA_card := Fintype.card_fin 2)
      (a_star := (0 : Fin 2))
      (A_rv := Phase2.traj_action (A := Fin 2) (O := Unit) t (Nat.lt_succ_self t))
      (X_rv := traj_prefix (A := Fin 2) (O := Unit) t (Nat.lt_succ_self t))
      (hAmeas := Phase2.measurable_traj_action t (Nat.lt_succ_self t))
      (hXmeas := measurable_traj_prefix t (Nat.lt_succ_self t))
      hH_ge'
  have h_rew_bound : ∀ s a, |Phase2.env₄.r (s, a)| ≤ 1 := by
    intro s a
    simp only [Phase2.env₄]
    split_ifs <;> norm_num
  have h_algValue := Phase2.algValue'_eq_sum Phase2.env₄ alg Phase2.env₄.hr_meas env₄_isMarkov hAlg h_rew_bound T
  have h_step_rew : ∀ t : Fin T,
      ∫ traj : Phase2.Trajectory (Fin 2) Unit T, (traj t).2.2 ∂(Phase2.trajMeasure Phase2.env₄ alg Phase2.env₄.hr_meas T) =
      (Phase2.trajMeasure Phase2.env₄ alg Phase2.env₄.hr_meas T {traj | (traj t).1 = 0}).toReal := by
    intro t
    have h_ae_rew := Phase2.trajMeasure_step_reward_eq_unit Phase2.env₄ alg Phase2.env₄.hr_meas Phase2.env₄_isDet.toTrans env₄_isMarkov hAlg T t.val t.isLt
    have h_int_eq : ∫ traj : Phase2.Trajectory (Fin 2) Unit T, (traj t).2.2 ∂Phase2.trajMeasure Phase2.env₄ alg Phase2.env₄.hr_meas T =
        ∫ traj : Phase2.Trajectory (Fin 2) Unit T, Phase2.env₄.r ((), (traj t).1) ∂Phase2.trajMeasure Phase2.env₄ alg Phase2.env₄.hr_meas T :=
      integral_congr_ae h_ae_rew
    rw [h_int_eq]
    have h_r_ind : (fun traj : Phase2.Trajectory (Fin 2) Unit T => Phase2.env₄.r ((), (traj t).1)) =
        {traj | (traj t).1 = 0}.indicator (fun _ => (1 : ℝ)) := by
      ext traj
      simp only [Phase2.env₄, Set.indicator_apply, Set.mem_setOf_eq]
    rw [h_r_ind]
    have hs_meas : MeasurableSet {traj : Phase2.Trajectory (Fin 2) Unit T | (traj t).1 = 0} :=
      (Phase2.measurable_traj_action t.val t.isLt) (measurableSet_singleton 0)
    rw [integral_indicator_const _ hs_meas]
    change ((Phase2.trajMeasure Phase2.env₄ alg Phase2.env₄.hr_meas T) {traj | (traj t).1 = 0}).toReal • (1 : ℝ) = _
    rw [smul_eq_mul, mul_one]
  have h_prob_sum : ∀ t : Fin T,
      (Phase2.trajMeasure Phase2.env₄ alg Phase2.env₄.hr_meas T {traj | (traj t).1 = 0}).toReal +
      (Phase2.trajMeasure Phase2.env₄ alg Phase2.env₄.hr_meas T {traj | (traj t).1 ≠ 0}).toReal = 1 := by
    intro t
    have hs0 : MeasurableSet {traj : Phase2.Trajectory (Fin 2) Unit T | (traj t).1 = 0} :=
      (Phase2.measurable_traj_action t.val t.isLt) (measurableSet_singleton 0)
    have hs1 : MeasurableSet {traj : Phase2.Trajectory (Fin 2) Unit T | (traj t).1 ≠ 0} :=
      hs0.compl
    have h_disj : Disjoint {traj : Phase2.Trajectory (Fin 2) Unit T | (traj t).1 = 0} {traj : Phase2.Trajectory (Fin 2) Unit T | (traj t).1 ≠ 0} :=
      disjoint_compl_right
    have h_union : {traj : Phase2.Trajectory (Fin 2) Unit T | (traj t).1 = 0} ∪ {traj : Phase2.Trajectory (Fin 2) Unit T | (traj t).1 ≠ 0} = Set.univ :=
      Set.union_compl_self _
    haveI h_prob_T := Phase2.trajMeasure_isProbability Phase2.env₄ alg Phase2.env₄.hr_meas env₄_isMarkov hAlg T
    have h_meas_add := measure_union h_disj hs1 (μ := Phase2.trajMeasure Phase2.env₄ alg Phase2.env₄.hr_meas T)
    rw [h_union, measure_univ] at h_meas_add
    have h_toReal : ((Phase2.trajMeasure Phase2.env₄ alg Phase2.env₄.hr_meas T {traj | (traj t).1 = 0}) + (Phase2.trajMeasure Phase2.env₄ alg Phase2.env₄.hr_meas T {traj | (traj t).1 ≠ 0})).toReal = (1 : ENNReal).toReal := by rw [← h_meas_add]
    rw [ENNReal.toReal_one, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at h_toReal
    exact h_toReal
  have h_marg_consist : ∀ t : Fin T,
      (Phase2.trajMeasure Phase2.env₄ alg Phase2.env₄.hr_meas T {traj | (traj t).1 ≠ 0}).toReal =
      (Phase2.trajMeasure Phase2.env₄ alg Phase2.env₄.hr_meas (t.val + 1) {traj | (traj ⟨t.val, Nat.lt_succ_self _⟩).1 ≠ 0}).toReal := by
    intro t
    have ht_le : t.val + 1 ≤ T := t.isLt
    have hE_meas : MeasurableSet {traj : Phase2.Trajectory (Fin 2) Unit (t.val + 1) | (traj ⟨t.val, Nat.lt_succ_self _⟩).1 ≠ 0} :=
      (Phase2.measurable_traj_action t.val (Nat.lt_succ_self _)) (measurableSet_singleton 0).compl
    have h_trunc := Phase2.trajMeasure_truncation Phase2.env₄ alg Phase2.env₄.hr_meas env₄_isMarkov hAlg T (t.val + 1) ht_le _ hE_meas
    have h_set_eq : {traj : Phase2.Trajectory (Fin 2) Unit T | (traj t).1 ≠ 0} =
        {traj : Phase2.Trajectory (Fin 2) Unit T | (fun i : Fin (t.val + 1) => traj (Fin.castLE ht_le i)) ∈ {traj' : Phase2.Trajectory (Fin 2) Unit (t.val + 1) | (traj' ⟨t.val, Nat.lt_succ_self _⟩).1 ≠ 0}} := by
      ext traj
      simp only [Set.mem_setOf_eq, ne_eq]
      rfl
    rw [h_set_eq]
    congr 1
  have h_regret_eq : regret Phase2.env₄ alg T = ∑ t : Fin T, (Phase2.trajMeasure Phase2.env₄ alg Phase2.env₄.hr_meas (t.val + 1) {traj | (traj ⟨t.val, Nat.lt_succ_self _⟩).1 ≠ 0}).toReal := by
    rw [Phase2.env₄_step_regret alg T]
    rw [SixPrimitives.algValue, h_algValue]
    have h_T_sum : (T : ℝ) = ∑ t : Fin T, (1 : ℝ) := by simp
    rw [h_T_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro t _
    rw [h_step_rew t]
    have h_sub : 1 - (Phase2.trajMeasure Phase2.env₄ alg Phase2.env₄.hr_meas T {traj | (traj t).1 = 0}).toReal = (Phase2.trajMeasure Phase2.env₄ alg Phase2.env₄.hr_meas T {traj | (traj t).1 ≠ 0}).toReal := by linarith [h_prob_sum t]
    rw [h_sub, h_marg_consist t]
  have h_split : ∑ t : Fin T, (Phase2.trajMeasure Phase2.env₄ alg Phase2.env₄.hr_meas (t.val + 1) {traj | (traj ⟨t.val, Nat.lt_succ_self _⟩).1 ≠ 0}).toReal ≥ ∑ t ∈ Finset.univ.filter (fun i : Fin T => t₀ ≤ i.val), (Phase2.trajMeasure Phase2.env₄ alg Phase2.env₄.hr_meas (t.val + 1) {traj | (traj ⟨t.val, Nat.lt_succ_self _⟩).1 ≠ 0}).toReal := by
    have h_eq := Finset.sum_filter_add_sum_filter_not Finset.univ (fun (i : Fin T) => t₀ ≤ i.val) (fun i => (Phase2.trajMeasure Phase2.env₄ alg Phase2.env₄.hr_meas (i.val + 1) {traj | (traj ⟨i.val, Nat.lt_succ_self _⟩).1 ≠ 0}).toReal)
    rw [← h_eq]
    apply le_add_of_nonneg_right
    apply Finset.sum_nonneg
    intro i _
    exact ENNReal.toReal_nonneg
  have h_tail_lower : ∑ t ∈ Finset.univ.filter (fun i : Fin T => t₀ ≤ i.val), Phase1.binEntropyInv (ε - η) ≤ ∑ t ∈ Finset.univ.filter (fun i : Fin T => t₀ ≤ i.val), (Phase2.trajMeasure Phase2.env₄ alg Phase2.env₄.hr_meas (t.val + 1) {traj | (traj ⟨t.val, Nat.lt_succ_self _⟩).1 ≠ 0}).toReal := by
    apply Finset.sum_le_sum
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
    exact h_fano t.val ht
  have h_card : (Finset.univ.filter (fun i : Fin T => t₀ ≤ i.val)).card = T - t₀ := by
    have hc : (Finset.univ.filter (fun i : Fin T => t₀ ≤ i.val)).card + (Finset.univ.filter (fun i : Fin T => i.val < t₀)).card = T := by
      have h_union : (Finset.univ.filter (fun i : Fin T => t₀ ≤ i.val)) ∪ (Finset.univ.filter (fun i : Fin T => i.val < t₀)) = Finset.univ := by
        ext x
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
        apply iff_true_intro
        omega
      have h_disj : Disjoint (Finset.univ.filter (fun i : Fin T => t₀ ≤ i.val)) (Finset.univ.filter (fun i : Fin T => i.val < t₀)) := by
        simp only [Finset.disjoint_left, Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
        intro x hx
        exact hx
      have h_sum := Finset.card_union_of_disjoint h_disj
      rw [h_union] at h_sum
      rw [← h_sum, Finset.card_univ, Fintype.card_fin]
    have hc2 : (Finset.univ.filter (fun i : Fin T => i.val < t₀)).card = t₀ := by
      let f_emb : Fin t₀ ↪ Fin T := ⟨fun i => ⟨i.val, by omega⟩, fun i j hij => by
        have h1 : (⟨i.val, by omega⟩ : Fin T).val = (⟨j.val, by omega⟩ : Fin T).val := congrArg Fin.val hij
        exact Fin.ext h1⟩
      have h_map : (Finset.univ : Finset (Fin t₀)).map f_emb = Finset.univ.filter (fun i : Fin T => i.val < t₀) := by
        ext x
        simp only [Finset.mem_map, Finset.mem_univ, true_and, Finset.mem_filter, f_emb, Function.Embedding.coeFn_mk]
        constructor
        · rintro ⟨i, rfl⟩
          exact i.isLt
        · intro hx
          refine ⟨⟨x.val, hx⟩, rfl⟩
      have hc3 := congrArg Finset.card h_map
      rw [Finset.card_map, Finset.card_univ, Fintype.card_fin] at hc3
      exact hc3.symm
    rw [hc2] at hc
    omega
  have h_sum_const : ∑ t ∈ Finset.univ.filter (fun i : Fin T => t₀ ≤ i.val), Phase1.binEntropyInv (ε - η) = Phase1.binEntropyInv (ε - η) * ((T : ℝ) - t₀) := by
    rw [Finset.sum_const, h_card, nsmul_eq_mul, mul_comm]
    have h_sub_cast : ((T - t₀ : ℕ) : ℝ) = (T : ℝ) - (t₀ : ℝ) := Nat.cast_sub hT
    rw [h_sub_cast]
  rw [h_regret_eq]
  calc Phase1.binEntropyInv (ε - η) * ((T : ℝ) - t₀)
    _ = ∑ t ∈ Finset.univ.filter (fun i : Fin T => t₀ ≤ i.val), Phase1.binEntropyInv (ε - η) := h_sum_const.symm
    _ ≤ ∑ t ∈ Finset.univ.filter (fun i : Fin T => t₀ ≤ i.val), (Phase2.trajMeasure Phase2.env₄ alg Phase2.env₄.hr_meas (t.val + 1) {traj | (traj ⟨t.val, Nat.lt_succ_self _⟩).1 ≠ 0}).toReal := h_tail_lower
    _ ≤ ∑ t : Fin T, (Phase2.trajMeasure Phase2.env₄ alg Phase2.env₄.hr_meas (t.val + 1) {traj | (traj ⟨t.val, Nat.lt_succ_self _⟩).1 ≠ 0}).toReal := h_split

theorem necessity_x4
    {Sig : Type*} [MeasurableSpace Sig] [TopologicalSpace Sig] [BorelSpace Sig]
    [MeasurableSingletonClass Sig] [MeasurableEq Sig]
    (alg : SixPrimitives.Algorithm (Fin 2) Unit Sig)
    (hAlg : Phase2.AlgIsMarkov alg)
    (hLacks : LacksX₄ (condEntSeqX4 alg)) :
    LinearRegret Phase2.env₄ alg := by
  unfold LacksX₄ at hLacks
  rcases hLacks with ⟨ε, hε_pos, hε_le⟩
  have h_ln2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let ε' := min ε (Real.log 2 / 2)
  have hε'_pos : 0 < ε' := lt_min hε_pos (half_pos h_ln2_pos)
  have hε'_lt : ε' < Real.log 2 := (min_le_right _ _).trans_lt (half_lt_self h_ln2_pos)
  have hε'_le : ε' ≤ liminf (condEntSeqX4 alg) atTop := (min_le_left _ _).trans hε_le
  let η := ε' / 2
  have hη_pos : 0 < η := half_pos hε'_pos
  have hη_lt : η < ε' := half_lt_self hε'_pos
  have h_bound := necessity_x4_explicit_bound ε' hε'_pos hε'_lt alg hAlg hε'_le η hη_pos hη_lt
  rcases h_bound with ⟨t₀, h_eventual⟩
  unfold LinearRegret
  use Phase1.binEntropyInv (ε' - η)
  constructor
  · have h1 : 0 < ε' - η := sub_pos.mpr hη_lt
    have h2 : ε' - η < Real.log 2 := by linarith
    exact (Phase1.binEntropyInv_spec h1 h2).1
  · use t₀

end NecessityX4

/-! # §5  Necessity of X₅ — Feasibility Projection -/

section NecessityX5

private noncomputable def env₅_isMarkov : Phase2.EnvIsMarkov Phase2.env₅ :=
  Phase2.envIsDeterministic_isMarkov Phase2.env₅ Phase2.env₅_isDet

noncomputable def infeasSet₅ : Set ℝ := (Phase2.feasSet₅)ᶜ

lemma measurableSet_feasSet₅ : MeasurableSet Phase2.feasSet₅ := by
  exact ((isClosed_Icc (a := (0 : ℝ)) (b := 1/3)).union
         (isClosed_Icc (a := (2/3 : ℝ)) (b := 1))).measurableSet

lemma measurableSet_infeasSet₅ : MeasurableSet infeasSet₅ :=
  MeasurableSet.compl measurableSet_feasSet₅

lemma eventual_ge_of_liminf_ge {f : ℕ → ℝ} {a : ℝ}
    (h_lt : a < liminf f atTop) (h_nonneg : ∀ n, 0 ≤ f n) :
    ∀ᶠ n in atTop, a ≤ f n := by
  have h_lb : ∀ᶠ n in atTop, (0 : ℝ) ≤ f n :=   -- ← named intermediate, type fully pinned
    Filter.Eventually.of_forall h_nonneg
  have hu : IsBoundedUnder (· ≥ ·) atTop f := ⟨0, h_lb⟩  -- ← now ⟨a, ha⟩ pattern works
  have h1 := Filter.eventually_lt_of_lt_liminf h_lt hu
  exact h1.mono fun t ht => ht.le

theorem necessity_x5_explicit_bound
    {Sig : Type*} [MeasurableSpace Sig] [TopologicalSpace Sig] [BorelSpace Sig]
    [MeasurableSingletonClass Sig] [MeasurableEq Sig]
    (δ : ℝ) (hδ : 0 < δ)
    (M : ℝ) (hM : 0 < M) (hM_le : M ≤ 1)
    (alg : SixPrimitives.Algorithm ℝ Unit Sig)
    (hAlg : Phase2.AlgIsMarkov alg)
    (hCesaro : δ ≤ liminf
      (fun T : ℕ => (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T,
        Phase2.infeasProbSeq Phase2.env₅ alg Phase2.env₅.hr_meas infeasSet₅ t)
      atTop) :
    ∀ᶠ T : ℕ in atTop,
      (1 + M) * (δ / 2) * T ≤ regret Phase2.env₅ alg T := by
  have h_liminf_gt : δ / 2 < liminf (fun T : ℕ => (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, Phase2.infeasProbSeq Phase2.env₅ alg Phase2.env₅.hr_meas infeasSet₅ t) atTop := by
    calc δ / 2 < δ := half_lt_self hδ
      _ ≤ _ := hCesaro
  have h_nonneg : ∀ T : ℕ, 0 ≤ (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, Phase2.infeasProbSeq Phase2.env₅ alg Phase2.env₅.hr_meas infeasSet₅ t := by
    intro T
    apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg T))
    apply Finset.sum_nonneg
    intro t _
    exact ENNReal.toReal_nonneg
  have h_eventual : ∀ᶠ T : ℕ in atTop, δ / 2 ≤ (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, Phase2.infeasProbSeq Phase2.env₅ alg Phase2.env₅.hr_meas infeasSet₅ t :=
    eventual_ge_of_liminf_ge h_liminf_gt h_nonneg
  have h_pos_T : ∀ᶠ T : ℕ in atTop, 0 < (T : ℝ) := by
    apply Filter.eventually_atTop.mpr
    use 1
    intro T hT
    exact Nat.cast_pos.mpr hT
  apply (h_eventual.and h_pos_T).mono
  intro T ⟨hT, hTpos⟩
  have h_opt : SixPrimitives.optValue Phase2.env₅ T = T := Phase2.env₅_optValue T
  have h_regret_eq : regret Phase2.env₅ alg T = (T : ℝ) - algValue Phase2.env₅ alg T := by
    unfold regret
    rw [h_opt]
  have h_step_bound : ∀ t : Fin T,
      ∫ traj : Phase2.Trajectory ℝ Unit T, (traj t).2.2 ∂Phase2.trajMeasure Phase2.env₅ alg Phase2.env₅.hr_meas T ≤
      1 - (1 + M) * Phase2.infeasProbSeq Phase2.env₅ alg Phase2.env₅.hr_meas infeasSet₅ t.val := by
    intro t
    have h_ae_rew := Phase2.trajMeasure_step_reward_eq_unit Phase2.env₅ alg Phase2.env₅.hr_meas Phase2.env₅_isDet.toTrans env₅_isMarkov hAlg T t.val t.isLt
    have h_int_eq : ∫ traj : Phase2.Trajectory ℝ Unit T, (traj t).2.2 ∂Phase2.trajMeasure Phase2.env₅ alg Phase2.env₅.hr_meas T =
        ∫ traj : Phase2.Trajectory ℝ Unit T, Phase2.env₅.r ((), (traj t).1) ∂Phase2.trajMeasure Phase2.env₅ alg Phase2.env₅.hr_meas T :=
      integral_congr_ae h_ae_rew
    rw [h_int_eq]
    have h_r_bound : ∀ a : ℝ, Phase2.env₅.r ((), a) ≤ 1 - (1 + M) * infeasSet₅.indicator (fun _ => (1 : ℝ)) a := by
      intro a
      have hp : Phase2.penalty₅ = 1 := rfl
      by_cases ha : a ∈ Phase2.feasSet₅
      · have h_ind : infeasSet₅.indicator (fun _ => (1 : ℝ)) a = 0 :=
          Set.indicator_of_notMem (by simp [infeasSet₅, ha]) _
        simp only [Phase2.env₅, if_pos ha, h_ind, mul_zero, sub_zero]
        apply max_le (by norm_num)
        linarith [le_min (abs_nonneg a) (abs_nonneg (1 - a))]
      · have h_ind : infeasSet₅.indicator (fun _ => (1 : ℝ)) a = 1 :=
          Set.indicator_of_mem (by simp [infeasSet₅, ha]) _
        simp only [Phase2.env₅, if_neg ha, h_ind, mul_one, hp]
        linarith [hM_le]
    have h_meas_a : Measurable (fun traj : Phase2.Trajectory ℝ Unit T => (traj t).1) := Phase2.measurable_traj_action t.val t.isLt
    have h_meas_r : Measurable (fun traj : Phase2.Trajectory ℝ Unit T => Phase2.env₅.r ((), (traj t).1)) :=
      Phase2.env₅.hr_meas.comp (measurable_const.prodMk h_meas_a)
    have hs : MeasurableSet ((fun traj : Phase2.Trajectory ℝ Unit T => (traj t).1) ⁻¹' infeasSet₅) := h_meas_a measurableSet_infeasSet₅
    haveI hProb : IsProbabilityMeasure (Phase2.trajMeasure Phase2.env₅ alg Phase2.env₅.hr_meas T) :=
      Phase2.trajMeasure_isProbability _ _ _ env₅_isMarkov hAlg T
    have h_int_1 : Integrable (fun traj : Phase2.Trajectory ℝ Unit T => (1 : ℝ)) (Phase2.trajMeasure Phase2.env₅ alg Phase2.env₅.hr_meas T) := integrable_const 1
    have h_int_ind : Integrable (((fun traj : Phase2.Trajectory ℝ Unit T => (traj t).1) ⁻¹' infeasSet₅).indicator (fun _ => (1 : ℝ))) (Phase2.trajMeasure Phase2.env₅ alg Phase2.env₅.hr_meas T) :=
      (integrable_const 1).indicator hs
    have h_int_rhs : Integrable (fun traj : Phase2.Trajectory ℝ Unit T => 1 - (1 + M) * ((fun traj => (traj t).1) ⁻¹' infeasSet₅).indicator (fun _ => (1 : ℝ)) traj) (Phase2.trajMeasure Phase2.env₅ alg Phase2.env₅.hr_meas T) :=
      h_int_1.sub (h_int_ind.const_mul (1 + M))
    have h_int_lhs : Integrable (fun traj : Phase2.Trajectory ℝ Unit T => Phase2.env₅.r ((), (traj t).1)) (Phase2.trajMeasure Phase2.env₅ alg Phase2.env₅.hr_meas T) := by
      apply Integrable.mono (integrable_const (1 : ℝ)) h_meas_r.aestronglyMeasurable
      filter_upwards with traj
      rw [Real.norm_eq_abs, abs_le]
      constructor
      · simp only [Phase2.env₅]
        split_ifs with ha
        · have h_min : 0 ≤ min |(traj t).1| |1 - (traj t).1| := le_min (abs_nonneg _) (abs_nonneg _)
          have h_max : 0 ≤ max 0 (1 - 3 * min |(traj t).1| |1 - (traj t).1|) := le_max_left _ _
          simp
        · have hp : Phase2.penalty₅ = (1 : ℝ) := rfl
          have h1 : ‖(1 : ℝ)‖ = (1 : ℝ) := norm_one
          linarith
      · simp only [Phase2.env₅]
        split_ifs with ha
        · have h_min : 0 ≤ min |(traj t).1| |1 - (traj t).1| := le_min (abs_nonneg _) (abs_nonneg _)
          apply max_le (by norm_num)
          simp
        · have hp : Phase2.penalty₅ = (1 : ℝ) := rfl
          have h1 : ‖(1 : ℝ)‖ = (1 : ℝ) := norm_one
          linarith
    have h_bound_int : ∫ traj : Phase2.Trajectory ℝ Unit T, Phase2.env₅.r ((), (traj t).1) ∂Phase2.trajMeasure Phase2.env₅ alg Phase2.env₅.hr_meas T ≤
        ∫ traj : Phase2.Trajectory ℝ Unit T, 1 - (1 + M) * ((fun traj => (traj t).1) ⁻¹' infeasSet₅).indicator (fun _ => (1 : ℝ)) traj ∂Phase2.trajMeasure Phase2.env₅ alg Phase2.env₅.hr_meas T := by
      apply integral_mono h_int_lhs h_int_rhs
      intro traj
      exact h_r_bound (traj t).1
    rw [integral_sub h_int_1 (h_int_ind.const_mul (1 + M))] at h_bound_int
    rw [integral_const] at h_bound_int
    simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul] at h_bound_int
    rw [integral_const_mul] at h_bound_int
    have h_ind_integral : ∫ traj : Phase2.Trajectory ℝ Unit T, ((fun traj => (traj t).1) ⁻¹' infeasSet₅).indicator (fun _ => (1 : ℝ)) traj ∂Phase2.trajMeasure Phase2.env₅ alg Phase2.env₅.hr_meas T =
      ((Phase2.trajMeasure Phase2.env₅ alg Phase2.env₅.hr_meas T) {traj | (traj t).1 ∈ infeasSet₅}).toReal := by
      rw [integral_indicator_const _ hs]
      simp only [smul_eq_mul, mul_one]
      rfl
    rw [h_ind_integral] at h_bound_int
    have h_infeas_seq : ((Phase2.trajMeasure Phase2.env₅ alg Phase2.env₅.hr_meas T) {traj | (traj t).1 ∈ infeasSet₅}).toReal =
                        Phase2.infeasProbSeq Phase2.env₅ alg Phase2.env₅.hr_meas infeasSet₅ t.val := by
      dsimp [Phase2.infeasProbSeq]
      have h_trunc := Phase2.trajMeasure_truncation Phase2.env₅ alg Phase2.env₅.hr_meas env₅_isMarkov hAlg T (t.val + 1) t.isLt
        {traj' | (traj' ⟨t.val, Nat.lt_succ_self t.val⟩).1 ∈ infeasSet₅}
        ((Phase2.measurable_traj_action t.val (Nat.lt_succ_self t.val)) measurableSet_infeasSet₅)
      have h_set_eq : {traj : Phase2.Trajectory ℝ Unit T | (traj t).1 ∈ infeasSet₅} =
                      {traj : Phase2.Trajectory ℝ Unit T | (fun i : Fin (t.val + 1) => traj (Fin.castLE t.isLt i)) ∈ {traj' : Phase2.Trajectory ℝ Unit (t.val + 1) | (traj' ⟨t.val, Nat.lt_succ_self t.val⟩).1 ∈ infeasSet₅}} := by
        ext traj
        simp only [Set.mem_setOf_eq, Fin.castLE_mk]
      rw [h_set_eq]
      exact congrArg ENNReal.toReal h_trunc
    rw [h_infeas_seq] at h_bound_int
    exact h_bound_int
  have h_alg_bound : algValue Phase2.env₅ alg T ≤ (T : ℝ) - (1 + M) * ∑ t ∈ Finset.range T, Phase2.infeasProbSeq Phase2.env₅ alg Phase2.env₅.hr_meas infeasSet₅ t := by
    unfold algValue
    have h_rew_bound : ∀ s a, |Phase2.env₅.r (s, a)| ≤ 1 := by
      intro s a
      simp only [Phase2.env₅]
      split_ifs
      · have h_min : 0 ≤ min |a| |1 - a| := le_min (abs_nonneg _) (abs_nonneg _)
        have h_max : max 0 (1 - 3 * min |a| |1 - a|) ≤ 1 :=
          max_le (by norm_num) (by linarith)
        rw [abs_of_nonneg (le_max_left _ _)]
        exact h_max
      · have hp : Phase2.penalty₅ = 1 := rfl
        rw [hp]; norm_num
    rw [Phase2.algValue'_eq_sum Phase2.env₅ alg Phase2.env₅.hr_meas env₅_isMarkov hAlg h_rew_bound T]
    have h_sum_le : (∑ t : Fin T, ∫ (traj : Phase2.Trajectory ℝ Unit T), (traj t).2.2 ∂Phase2.trajMeasure Phase2.env₅ alg Phase2.env₅.hr_meas T) ≤
                    ∑ t : Fin T, (1 - (1 + M) * Phase2.infeasProbSeq Phase2.env₅ alg Phase2.env₅.hr_meas infeasSet₅ t.val) := by
      apply Finset.sum_le_sum
      intro t _
      exact h_step_bound t
    have h_sum_eq : (∑ t : Fin T, (1 - (1 + M) * Phase2.infeasProbSeq Phase2.env₅ alg Phase2.env₅.hr_meas infeasSet₅ t.val)) =
                    (T : ℝ) - (1 + M) * ∑ t ∈ Finset.range T, Phase2.infeasProbSeq Phase2.env₅ alg Phase2.env₅.hr_meas infeasSet₅ t := by
      rw [Finset.sum_sub_distrib]
      have h_ones : (∑ t : Fin T, (1 : ℝ)) = (T : ℝ) := by simp
      rw [h_ones, ← Finset.mul_sum]
      congr 1
      rw [Fin.sum_univ_eq_sum_range
        (fun t => Phase2.infeasProbSeq Phase2.env₅ alg Phase2.env₅.hr_meas infeasSet₅ t) T]
    linarith
  rw [h_regret_eq]
  calc (1 + M) * (δ / 2) * T
    _ = (1 + M) * ((δ / 2) * T) := by ring
    _ = (1 + M) * (T * (δ / 2)) := by ring
    _ ≤ (1 + M) * (T * ((T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, Phase2.infeasProbSeq Phase2.env₅ alg Phase2.env₅.hr_meas infeasSet₅ t)) := by
      apply mul_le_mul_of_nonneg_left
      · apply mul_le_mul_of_nonneg_left hT (Nat.cast_nonneg T)
      · linarith [hM]
    _ = (1 + M) * (T * (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, Phase2.infeasProbSeq Phase2.env₅ alg Phase2.env₅.hr_meas infeasSet₅ t) := by ring
    _ = (1 + M) * (1 * ∑ t ∈ Finset.range T, Phase2.infeasProbSeq Phase2.env₅ alg Phase2.env₅.hr_meas infeasSet₅ t) := by
      rw [mul_inv_cancel₀ hTpos.ne']
    _ = (1 + M) * ∑ t ∈ Finset.range T, Phase2.infeasProbSeq Phase2.env₅ alg Phase2.env₅.hr_meas infeasSet₅ t := by ring
    _ = (T : ℝ) - ((T : ℝ) - (1 + M) * ∑ t ∈ Finset.range T, Phase2.infeasProbSeq Phase2.env₅ alg Phase2.env₅.hr_meas infeasSet₅ t) := by ring
    _ ≤ (T : ℝ) - algValue Phase2.env₅ alg T := sub_le_sub_left h_alg_bound (T : ℝ)

theorem necessity_x5
    {Sig : Type*} [MeasurableSpace Sig] [TopologicalSpace Sig] [BorelSpace Sig]
    [MeasurableSingletonClass Sig] [MeasurableEq Sig]
    (alg : SixPrimitives.Algorithm ℝ Unit Sig)
    (hAlg : Phase2.AlgIsMarkov alg)
    (hLacks : LacksX₅ (Phase2.infeasProbSeq
        Phase2.env₅ alg Phase2.env₅.hr_meas infeasSet₅)) :
    LinearRegret Phase2.env₅ alg := by
  unfold LacksX₅ at hLacks
  rcases hLacks with ⟨δ, hδ_pos, hCesaro⟩
  -- env₅ penalty M is 1 (defined in Phase2)
  have hM_pos : 0 < (1 : ℝ) := zero_lt_one
  have h_bound := necessity_x5_explicit_bound δ hδ_pos 1 hM_pos le_rfl alg hAlg hCesaro
  unfold LinearRegret
  use (1 + 1) * (δ / 2)
  constructor
  · have h1 : 0 < (1 + 1 : ℝ) := by norm_num
    have h2 : 0 < δ / 2 := half_pos hδ_pos
    exact mul_pos h1 h2
  · use 0
    apply h_bound.mono
    intro T hT
    simp only [Nat.cast_zero, sub_zero]
    exact hT

end NecessityX5

/-! # §6  Necessity of X₆ — Feedback Adaptation -/

section NecessityX6

open Classical in
noncomputable def env₆_nonstat (T : ℕ) (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ4 : Δ ≤ 1/4) :
    SixPrimitives.Env ℕ (Fin 2) Bool where
  trans := Kernel.deterministic (fun (s, _) => s + 1) (by measurability)
  obs := {
    toFun := fun (s, a) =>
      let postCP : Prop := T / 2 < s
      if (a = (0 : Fin 2)) = postCP
      then Phase2.bernoulliMeasure (1/2 + Δ) (by linarith) (by linarith)
      else Phase2.bernoulliMeasure (1/2 - Δ) (by linarith) (by linarith)
    measurable' := measurable_of_countable _
  }
  r := fun (s, a) =>
    let postCP : Prop := T / 2 < s
    if (a = (0 : Fin 2)) = postCP then 1/2 + Δ else 1/2 - Δ
  hr_meas := measurable_of_countable _
  μ₀ := Measure.dirac 0
  hμ₀ := inferInstance

instance env₆_nonstat_isMarkov (T : ℕ) (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ4 : Δ ≤ 1/4) :
    Phase2.EnvIsMarkov (env₆_nonstat T Δ hΔ0 hΔ4) where
  trans_markov := ⟨fun _ => by dsimp [env₆_nonstat]; infer_instance⟩
  obs_markov := ⟨fun ⟨s, a⟩ => by
    change IsProbabilityMeasure (if (a = (0 : Fin 2)) = (T / 2 < s) then _ else _)
    split_ifs
    · exact Phase2.bernoulliMeasure_isProbability _ _ _
    · exact Phase2.bernoulliMeasure_isProbability _ _ _⟩

noncomputable def env₆_nonstat_transDet (T : ℕ) (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ4 : Δ ≤ 1/4) :
    Phase2.TransIsDeterministic (env₆_nonstat T Δ hΔ0 hΔ4) where
  s₀ := 0
  μ₀_eq := rfl
  transFn := fun p => p.1 + 1
  transFn_meas := measurable_fst.add measurable_const
  trans_eq := fun _ => rfl

lemma env₆_state_t_eq (T : ℕ) (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ4 : Δ ≤ 1/4)
    {t_len : ℕ} (ω : Phase2.Trajectory (Fin 2) Bool t_len) (t : ℕ) (ht : t ≤ t_len) :
    Phase2.state_t (env₆_nonstat T Δ hΔ0 hΔ4) (env₆_nonstat_transDet T Δ hΔ0 hΔ4) ω t = t := by
  induction t with
  | zero =>
    rw [Phase2.state_t_zero]
    rfl
  | succ t ih =>
    have h_lt : t < t_len := by omega
    rw [Phase2.state_t_succ _ _ _ t h_lt]
    change Phase2.state_t (env₆_nonstat T Δ hΔ0 hΔ4) (env₆_nonstat_transDet T Δ hΔ0 hΔ4) ω t + 1 = t + 1
    rw [ih (by omega)]

noncomputable def env₆_optAlg (T : ℕ) : SixPrimitives.Algorithm (Fin 2) Bool ℕ where
  act := Kernel.deterministic (fun σ => if σ ≤ T / 2 then 1 else 0) (by measurability)
  update := Kernel.deterministic (fun ⟨σ, _, _, _⟩ => σ + 1) (by measurability)
  σ₀ := 0

instance env₆_optAlg_isDet (T : ℕ) : Phase2.AlgIsDeterministic (env₆_optAlg T) where
  actFn := fun σ => if σ ≤ T / 2 then 1 else 0
  actFn_meas := by measurability
  act_eq := fun _ => rfl
  updateFn := fun ⟨σ, _, _, _⟩ => σ + 1
  updateFn_meas := by measurability
  update_eq := fun _ => rfl

lemma env₆_summary_t_eq (T : ℕ) {t_len : ℕ} (ω : Phase2.Trajectory (Fin 2) Bool t_len) (t : ℕ) (ht : t ≤ t_len) :
    Phase2.summary_t (env₆_optAlg T) t (fun i => ω (Fin.castLE ht i)) = t := by
  induction t with
  | zero =>
    rw [Phase2.summary_t_zero]
    rfl
  | succ t ih =>
    rw [Phase2.summary_t_succ]
    change Phase2.summary_t (env₆_optAlg T) t _ + 1 = t + 1
    have h_cast : (fun (i : Fin t) => ω (Fin.castLE ht (Fin.castSucc i))) =
                  (fun (i : Fin t) => ω (Fin.castLE (by omega) i)) := by
      funext i
      have h_fin_eq : Fin.castLE ht (Fin.castSucc i) = Fin.castLE (by omega) i := by
        apply Fin.ext; rfl
      rw [h_fin_eq]
    rw [h_cast]
    rw [ih (by omega)]

lemma env₆_optValue (T : ℕ) (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ4 : Δ ≤ 1/4) :
    SixPrimitives.optValue (env₆_nonstat T Δ hΔ0 hΔ4) T = (1 / 2 + Δ) * T := by
  have hEnv := env₆_nonstat_isMarkov T Δ hΔ0 hΔ4
  have hAlg := Phase2.algIsDeterministic_isMarkov (env₆_optAlg T)
  have h_bound : ∀ (v : ℝ), v ∈ {x : ℝ | ∃ (Sig : Type) (_ : MeasurableSpace Sig) (_ : TopologicalSpace Sig) (_ : BorelSpace Sig) (alg : SixPrimitives.Algorithm (Fin 2) Bool Sig) (_ : IsMarkovKernel alg.act) (_ : IsMarkovKernel alg.update), x = Phase2.algValue' (env₆_nonstat T Δ hΔ0 hΔ4) alg (env₆_nonstat T Δ hΔ0 hΔ4).hr_meas T} → v ≤ (1 / 2 + Δ) * (T : ℝ) := by
    rintro v ⟨Sig, hSigM, hSigT, hSigB, alg, hAct, hUpd, rfl⟩
    have h_rew_bound : ∀ (s : ℕ) (a : Fin 2), |(env₆_nonstat T Δ hΔ0 hΔ4).r (s, a)| ≤ 1 / 2 + Δ := by
      intro s a
      dsimp [env₆_nonstat]
      split_ifs
      · rw [abs_of_pos (by linarith)]
      · rw [abs_of_pos (by linarith)]; linarith
    have h_val := Phase2.algValue'_le_const (env₆_nonstat T Δ hΔ0 hΔ4) alg (env₆_nonstat T Δ hΔ0 hΔ4).hr_meas hEnv { act_markov := hAct, update_markov := hUpd } T (1 / 2 + Δ) h_rew_bound
    linarith
  unfold SixPrimitives.optValue
  apply le_antisymm
  · apply csSup_le
    · use Phase2.algValue' (env₆_nonstat T Δ hΔ0 hΔ4) (env₆_optAlg T) (env₆_nonstat T Δ hΔ0 hΔ4).hr_meas T
      exact ⟨ℕ, inferInstance, inferInstance, inferInstance, env₆_optAlg T, hAlg.act_markov, hAlg.update_markov, rfl⟩
    · exact h_bound
  · apply le_csSup
    · exact ⟨(1 / 2 + Δ) * T, h_bound⟩
    · refine ⟨ℕ, inferInstance, inferInstance, inferInstance, env₆_optAlg T, hAlg.act_markov, hAlg.update_markov, ?_⟩
      symm
      dsimp [Phase2.algValue']
      let hTransDet := env₆_nonstat_transDet T Δ hΔ0 hΔ4
      have h_eq_step : ∀ t : Fin T, ∀ᵐ ω ∂(Phase2.trajMeasure (env₆_nonstat T Δ hΔ0 hΔ4) (env₆_optAlg T) (env₆_nonstat T Δ hΔ0 hΔ4).hr_meas T),
          (ω t).2.2 = (env₆_nonstat T Δ hΔ0 hΔ4).r (Phase2.state_t (env₆_nonstat T Δ hΔ0 hΔ4) hTransDet ω t.val, (ω t).1) :=
        fun t => Phase2.trajMeasure_step_reward_eq (env₆_nonstat T Δ hΔ0 hΔ4) (env₆_optAlg T) (env₆_nonstat T Δ hΔ0 hΔ4).hr_meas hTransDet hEnv hAlg T t.val t.isLt
      have h_act : ∀ t : Fin T, ∀ᵐ ω ∂(Phase2.trajMeasure (env₆_nonstat T Δ hΔ0 hΔ4) (env₆_optAlg T) (env₆_nonstat T Δ hΔ0 hΔ4).hr_meas T),
          (ω t).1 = if Phase2.summary_at (env₆_optAlg T) t.val T (Nat.le_of_lt t.isLt) ω ≤ T / 2 then 1 else 0 := by
        intro t
        filter_upwards [Phase2.traj_action_ae_eq_actFn (env₆_nonstat T Δ hΔ0 hΔ4) (env₆_optAlg T) (env₆_nonstat T Δ hΔ0 hΔ4).hr_meas t.val T t.isLt hEnv] with ω hω
        exact hω
      have h_sum_eq : ∀ (t : Fin T) (ω : Phase2.Trajectory (Fin 2) Bool T), Phase2.summary_at (env₆_optAlg T) t.val T (Nat.le_of_lt t.isLt) ω = t.val := by
        intro t ω
        dsimp [Phase2.summary_at]
        exact env₆_summary_t_eq T ω t.val (Nat.le_of_lt t.isLt)
      have h_state_eq : ∀ (t : Fin T) (ω : Phase2.Trajectory (Fin 2) Bool T), Phase2.state_t (env₆_nonstat T Δ hΔ0 hΔ4) hTransDet ω t.val = t.val := by
        intro t ω
        exact env₆_state_t_eq T Δ hΔ0 hΔ4 ω t.val (Nat.le_of_lt t.isLt)
      have h_all : ∀ᵐ ω ∂(Phase2.trajMeasure (env₆_nonstat T Δ hΔ0 hΔ4) (env₆_optAlg T) (env₆_nonstat T Δ hΔ0 hΔ4).hr_meas T),
          ∀ t : Fin T, (ω t).2.2 = 1/2 + Δ := by
        rw [ae_all_iff]
        intro t
        filter_upwards [h_eq_step t, h_act t] with ω h_unit h_act_eq
        rw [h_unit, h_act_eq, h_sum_eq t ω, h_state_eq t ω]
        dsimp [env₆_nonstat]
        by_cases h_cp : t.val ≤ T / 2
        · rw [if_pos h_cp]
          have h_post : (T / 2 < t.val) ↔ False := iff_false_intro (by omega)
          have h10 : ((1 : Fin 2) = 0) ↔ False := by decide
          simp [h_post, h10]
        · rw [if_neg h_cp]
          have h_post : (T / 2 < t.val) ↔ True := iff_true_intro (by omega)
          have h00 : ((0 : Fin 2) = 0) ↔ True := by decide
          simp [h_post]
      have h_rew : ∀ᵐ traj ∂(Phase2.trajMeasure (env₆_nonstat T Δ hΔ0 hΔ4) (env₆_optAlg T) (env₆_nonstat T Δ hΔ0 hΔ4).hr_meas T),
          ∑ t : Fin T, (traj t).2.2 = (T : ℝ) * (1/2 + Δ) := by
        filter_upwards [h_all] with ω hω
        calc ∑ t : Fin T, (ω t).2.2
          _ = ∑ t : Fin T, (1/2 + Δ : ℝ) := Finset.sum_congr rfl (fun t _ => hω t)
          _ = (T : ℝ) * (1/2 + Δ) := by
            simp
            ring
      haveI : IsProbabilityMeasure (Phase2.trajMeasure (env₆_nonstat T Δ hΔ0 hΔ4) (env₆_optAlg T) (env₆_nonstat T Δ hΔ0 hΔ4).hr_meas T) :=
        Phase2.trajMeasure_isProbability _ _ _ hEnv hAlg T
      have h_int_eq : ∫ (traj : Phase2.Trajectory (Fin 2) Bool T), ∑ t : Fin T, (traj t).2.2 ∂Phase2.trajMeasure (env₆_nonstat T Δ hΔ0 hΔ4) (env₆_optAlg T) (env₆_nonstat T Δ hΔ0 hΔ4).hr_meas T = ∫ (traj : Phase2.Trajectory (Fin 2) Bool T), (T : ℝ) * (1/2 + Δ) ∂Phase2.trajMeasure (env₆_nonstat T Δ hΔ0 hΔ4) (env₆_optAlg T) (env₆_nonstat T Δ hΔ0 hΔ4).hr_meas T := integral_congr_ae h_rew
      rw [h_int_eq, integral_const]
      simp [mul_comm]

lemma window_length_lower_bound (T : ℕ) (ε : ℝ) (hε0 : 0 < ε) (tau : ℕ) (htau : tau = T / 2) :
    (ε / 2) * (T : ℝ) - (ε / 2 + 1) ≤ (Nat.floor ((1 + ε) * (tau : ℝ)) - tau : ℝ) := by
  have h_pos : 0 ≤ (1 + ε) * (tau : ℝ) := by
    apply mul_nonneg
    · linarith
    · exact Nat.cast_nonneg tau
  have h_floor_lt := Nat.lt_floor_add_one ((1 + ε) * (tau : ℝ))
  have h_floor : (1 + ε) * (tau : ℝ) - 1 ≤ (Nat.floor ((1 + ε) * (tau : ℝ)) : ℝ) := by linarith
  have h_tau_lb : (T : ℝ) / 2 - 1 / 2 ≤ (tau : ℝ) := by
    rw [htau]
    have h_mod : T % 2 = 0 ∨ T % 2 = 1 := by omega
    rcases h_mod with h0 | h1
    · have h_mul : 2 * (T / 2) = T := by omega
      have h_mul_r : 2 * ((T / 2 : ℕ) : ℝ) = (T : ℝ) := by exact_mod_cast h_mul
      linarith
    · have h_mul : 2 * (T / 2) + 1 = T := by omega
      have h_mul_r : 2 * ((T / 2 : ℕ) : ℝ) + 1 = (T : ℝ) := by exact_mod_cast h_mul
      linarith
  calc (ε / 2) * (T : ℝ) - (ε / 2 + 1)
    _ = ε * ((T : ℝ) / 2 - 1 / 2) - 1 := by ring
    _ ≤ ε * (tau : ℝ) - 1 := by
      apply sub_le_sub_right
      apply mul_le_mul_of_nonneg_left h_tau_lb hε0.le
    _ = (1 + ε) * (tau : ℝ) - 1 - (tau : ℝ) := by ring
    _ ≤ (Nat.floor ((1 + ε) * (tau : ℝ)) : ℝ) - (tau : ℝ) := sub_le_sub_right h_floor _

lemma staleProbSeq_eq_actionMarginal
    {Sig : Type} [MeasurableSpace Sig] [TopologicalSpace Sig] [BorelSpace Sig]
    [MeasurableSingletonClass Sig] [MeasurableEq Sig]
    (T : ℕ) (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ4 : Δ ≤ 1 / 4)
    (alg : SixPrimitives.Algorithm (Fin 2) Bool Sig)
    (hAlg : Phase2.AlgIsMarkov alg) (t : ℕ) :
    Phase2.staleProbSeq (env₆_nonstat T Δ hΔ0 hΔ4) alg (env₆_nonstat T Δ hΔ0 hΔ4).hr_meas 1 t =
    (Phase2.actionMarginal (env₆_nonstat T Δ hΔ0 hΔ4) alg (env₆_nonstat T Δ hΔ0 hΔ4).hr_meas (env₆_nonstat_isMarkov T Δ hΔ0 hΔ4) hAlg (t + 1) ⟨t, Nat.lt_succ_self t⟩ {1}).toReal := by
  dsimp [Phase2.staleProbSeq, Phase2.actionMarginal]
  have h_meas : Measurable (fun (traj : Phase2.Trajectory (Fin 2) Bool (t + 1)) => (traj ⟨t, Nat.lt_succ_self t⟩).1) := Phase2.measurable_traj_action t (Nat.lt_succ_self t)
  rw [Measure.map_apply h_meas (measurableSet_singleton 1)]
  rfl

lemma env₆_step_reward_le_opt
    {Sig : Type} [MeasurableSpace Sig] [TopologicalSpace Sig] [BorelSpace Sig]
    [MeasurableSingletonClass Sig] [MeasurableEq Sig]
    (T : ℕ) (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ4 : Δ ≤ 1 / 4)
    (alg : SixPrimitives.Algorithm (Fin 2) Bool Sig)
    (hAlg : Phase2.AlgIsMarkov alg)
    (t : Fin T) :
    ∫ traj : Phase2.Trajectory (Fin 2) Bool T, (traj t).2.2 ∂(Phase2.trajMeasure (env₆_nonstat T Δ hΔ0 hΔ4) alg (env₆_nonstat T Δ hΔ0 hΔ4).hr_meas T) ≤
    1 / 2 + Δ := by
  let env := env₆_nonstat T Δ hΔ0 hΔ4
  have hEnv := env₆_nonstat_isMarkov T Δ hΔ0 hΔ4
  have hTrans := env₆_nonstat_transDet T Δ hΔ0 hΔ4
  have h_ae_rew := Phase2.trajMeasure_step_reward_eq env alg env.hr_meas hTrans hEnv hAlg T t.val t.isLt
  have h_int_eq : ∫ traj : Phase2.Trajectory (Fin 2) Bool T, (traj t).2.2 ∂Phase2.trajMeasure env alg env.hr_meas T =
      ∫ traj : Phase2.Trajectory (Fin 2) Bool T, env.r (Phase2.state_t env hTrans traj t.val, (traj t).1) ∂Phase2.trajMeasure env alg env.hr_meas T :=
    integral_congr_ae h_ae_rew
  rw [h_int_eq]
  have h_r_bound : ∀ s a, env.r (s, a) ≤ 1 / 2 + Δ := by
    intro s a
    change (env₆_nonstat T Δ hΔ0 hΔ4).r (s, a) ≤ 1 / 2 + Δ
    dsimp [env₆_nonstat]
    split_ifs
    · rfl
    · linarith
  have h_bound_ae : ∀ᵐ traj ∂Phase2.trajMeasure env alg env.hr_meas T, env.r (Phase2.state_t env hTrans traj t.val, (traj t).1) ≤ 1 / 2 + Δ := by
    apply Filter.Eventually.of_forall
    intro traj
    exact h_r_bound _ _
  haveI hProb := Phase2.trajMeasure_isProbability env alg env.hr_meas hEnv hAlg T
  have h_meas_r : Measurable (fun traj : Phase2.Trajectory (Fin 2) Bool T => env.r (Phase2.state_t env hTrans traj t.val, (traj t).1)) := by
    have h_s := Phase2.measurable_state_t env hTrans T t.val
    have h_a := Phase2.measurable_traj_action (A := Fin 2) (O := Bool) t.val t.isLt
    exact env.hr_meas.comp (h_s.prodMk h_a)
  have h_int_lhs : Integrable (fun traj : Phase2.Trajectory (Fin 2) Bool T => env.r (Phase2.state_t env hTrans traj t.val, (traj t).1)) (Phase2.trajMeasure env alg env.hr_meas T) := by
    apply Integrable.mono (integrable_const (1 / 2 + Δ)) h_meas_r.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro traj
    have h_pos : 0 ≤ 1 / 2 + Δ := by linarith
    rw [Real.norm_eq_abs, Real.norm_of_nonneg h_pos]
    have hr_le := h_r_bound (Phase2.state_t env hTrans traj t.val) (traj t).1
    have hr_ge : -(1/2 + Δ) ≤ env.r (Phase2.state_t env hTrans traj t.val, (traj t).1) := by
      change -(1/2 + Δ) ≤ (env₆_nonstat T Δ hΔ0 hΔ4).r _
      dsimp [env₆_nonstat]
      split_ifs <;> linarith
    exact abs_le.mpr ⟨hr_ge, hr_le⟩
  have h_int_const : ∫ traj : Phase2.Trajectory (Fin 2) Bool T, (1 / 2 + Δ) ∂Phase2.trajMeasure env alg env.hr_meas T = 1 / 2 + Δ := by
    rw [integral_const]
    simp
  rw [← h_int_const]
  exact integral_mono_ae h_int_lhs (integrable_const _) h_bound_ae

lemma env₆_post_cp_reward_bound
    {Sig : Type} [MeasurableSpace Sig] [TopologicalSpace Sig] [BorelSpace Sig]
    [MeasurableSingletonClass Sig] [MeasurableEq Sig]
    (T : ℕ) (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ4 : Δ ≤ 1 / 4)
    (alg : SixPrimitives.Algorithm (Fin 2) Bool Sig)
    (hAlg : Phase2.AlgIsMarkov alg)
    (t : Fin T) (ht_post : T / 2 < t.val)
    (δ : ℝ) (_hδ : 0 < δ)
    (h_stale : 1 / 2 + δ ≤ (Phase2.actionMarginal (env₆_nonstat T Δ hΔ0 hΔ4) alg (env₆_nonstat T Δ hΔ0 hΔ4).hr_meas (env₆_nonstat_isMarkov T Δ hΔ0 hΔ4) hAlg (t.val + 1) ⟨t.val, Nat.lt_succ_self _⟩ {1}).toReal) :
    ∫ traj : Phase2.Trajectory (Fin 2) Bool T, (traj t).2.2 ∂(Phase2.trajMeasure (env₆_nonstat T Δ hΔ0 hΔ4) alg (env₆_nonstat T Δ hΔ0 hΔ4).hr_meas T) ≤
    1 / 2 - 2 * δ * Δ := by
  have hEnv := env₆_nonstat_isMarkov T Δ hΔ0 hΔ4
  let hTrans := env₆_nonstat_transDet T Δ hΔ0 hΔ4
  have h_ae_rew := Phase2.trajMeasure_step_reward_eq (env₆_nonstat T Δ hΔ0 hΔ4) alg (env₆_nonstat T Δ hΔ0 hΔ4).hr_meas hTrans hEnv hAlg T t.val t.isLt
  have h_int_eq : ∫ traj : Phase2.Trajectory (Fin 2) Bool T, (traj t).2.2 ∂Phase2.trajMeasure (env₆_nonstat T Δ hΔ0 hΔ4) alg (env₆_nonstat T Δ hΔ0 hΔ4).hr_meas T =
      ∫ traj : Phase2.Trajectory (Fin 2) Bool T, (env₆_nonstat T Δ hΔ0 hΔ4).r (Phase2.state_t (env₆_nonstat T Δ hΔ0 hΔ4) hTrans traj t.val, (traj t).1) ∂Phase2.trajMeasure (env₆_nonstat T Δ hΔ0 hΔ4) alg (env₆_nonstat T Δ hΔ0 hΔ4).hr_meas T :=
    integral_congr_ae h_ae_rew
  rw [h_int_eq]
  have h_state_eq : ∀ traj, Phase2.state_t (env₆_nonstat T Δ hΔ0 hΔ4) hTrans traj t.val = t.val := fun traj => env₆_state_t_eq T Δ hΔ0 hΔ4 traj t.val (Nat.le_of_lt t.isLt)
  have h_r_expand : (fun traj : Phase2.Trajectory (Fin 2) Bool T => (env₆_nonstat T Δ hΔ0 hΔ4).r (Phase2.state_t (env₆_nonstat T Δ hΔ0 hΔ4) hTrans traj t.val, (traj t).1)) =
      (fun traj => (1 / 2 + Δ) * ({traj' : Phase2.Trajectory (Fin 2) Bool T | (traj' t).1 = 0}.indicator (fun _ => (1 : ℝ)) traj) +
                   (1 / 2 - Δ) * ({traj' : Phase2.Trajectory (Fin 2) Bool T | (traj' t).1 = 1}.indicator (fun _ => (1 : ℝ)) traj)) := by
    ext traj
    rw [h_state_eq traj]
    dsimp [env₆_nonstat]
    have h_post : (T / 2 < t.val) ↔ True := iff_true_intro ht_post
    simp only [h_post, Set.indicator_apply, Set.mem_setOf_eq]
    by_cases h0 : (traj t).1 = 0
    · simp [h0]
    · have h1 : (traj t).1.val = 1 := by
        have h_val := (traj t).1.val
        have h_lt := (traj t).1.isLt
        have h_neq : (traj t).1.val ≠ 0 := by intro contra; apply h0; exact Fin.ext contra
        omega
      have h1_ext : (traj t).1 = 1 := Fin.ext h1
      have h10 : ((1 : Fin 2) = 0) ↔ False := by decide
      simp [h1_ext, h10]
  rw [h_r_expand]
  have hs0_meas : MeasurableSet {traj' : Phase2.Trajectory (Fin 2) Bool T | (traj' t).1 = 0} :=
    (Phase2.measurable_traj_action t.val t.isLt) (measurableSet_singleton 0)
  have hs1_meas : MeasurableSet {traj' : Phase2.Trajectory (Fin 2) Bool T | (traj' t).1 = 1} :=
    (Phase2.measurable_traj_action t.val t.isLt) (measurableSet_singleton 1)
  haveI h_prob : IsProbabilityMeasure (Phase2.trajMeasure (env₆_nonstat T Δ hΔ0 hΔ4) alg (env₆_nonstat T Δ hΔ0 hΔ4).hr_meas T) :=
    Phase2.trajMeasure_isProbability (env₆_nonstat T Δ hΔ0 hΔ4) alg (env₆_nonstat T Δ hΔ0 hΔ4).hr_meas hEnv hAlg T
  have h_int_add : Integrable (fun traj : Phase2.Trajectory (Fin 2) Bool T => (1 / 2 + Δ) * {traj' : Phase2.Trajectory (Fin 2) Bool T | (traj' t).1 = 0}.indicator (fun _ => (1 : ℝ)) traj) (Phase2.trajMeasure (env₆_nonstat T Δ hΔ0 hΔ4) alg (env₆_nonstat T Δ hΔ0 hΔ4).hr_meas T) :=
    ((integrable_const (1:ℝ)).indicator hs0_meas).const_mul (1 / 2 + Δ)
  have h_int_add2 : Integrable (fun traj : Phase2.Trajectory (Fin 2) Bool T => (1 / 2 - Δ) * {traj' : Phase2.Trajectory (Fin 2) Bool T | (traj' t).1 = 1}.indicator (fun _ => (1 : ℝ)) traj) (Phase2.trajMeasure (env₆_nonstat T Δ hΔ0 hΔ4) alg (env₆_nonstat T Δ hΔ0 hΔ4).hr_meas T) :=
    ((integrable_const (1:ℝ)).indicator hs1_meas).const_mul (1 / 2 - Δ)
  rw [integral_add h_int_add h_int_add2]
  rw [integral_const_mul, integral_const_mul]
  have h_ind0 : ∫ traj, {traj' : Phase2.Trajectory (Fin 2) Bool T | (traj' t).1 = 0}.indicator (fun _ => (1 : ℝ)) traj ∂Phase2.trajMeasure (env₆_nonstat T Δ hΔ0 hΔ4) alg (env₆_nonstat T Δ hΔ0 hΔ4).hr_meas T = (Phase2.trajMeasure (env₆_nonstat T Δ hΔ0 hΔ4) alg (env₆_nonstat T Δ hΔ0 hΔ4).hr_meas T {traj' | (traj' t).1 = 0}).toReal := by
    rw [integral_indicator_const _ hs0_meas]
    simp only [smul_eq_mul, mul_one]
    rfl
  have h_ind1 : ∫ traj, {traj' : Phase2.Trajectory (Fin 2) Bool T | (traj' t).1 = 1}.indicator (fun _ => (1 : ℝ)) traj ∂Phase2.trajMeasure (env₆_nonstat T Δ hΔ0 hΔ4) alg (env₆_nonstat T Δ hΔ0 hΔ4).hr_meas T = (Phase2.trajMeasure (env₆_nonstat T Δ hΔ0 hΔ4) alg (env₆_nonstat T Δ hΔ0 hΔ4).hr_meas T {traj' | (traj' t).1 = 1}).toReal := by
    rw [integral_indicator_const _ hs1_meas]
    simp only [smul_eq_mul, mul_one]
    rfl
  rw [h_ind0, h_ind1]
  have h_marg0_eq : (Phase2.trajMeasure (env₆_nonstat T Δ hΔ0 hΔ4) alg (env₆_nonstat T Δ hΔ0 hΔ4).hr_meas T {traj' | (traj' t).1 = 0}).toReal =
    (Phase2.actionMarginal (env₆_nonstat T Δ hΔ0 hΔ4) alg (env₆_nonstat T Δ hΔ0 hΔ4).hr_meas hEnv hAlg (t.val + 1) ⟨t.val, Nat.lt_succ_self _⟩ {0}).toReal := by
    have ht_le : t.val + 1 ≤ T := t.isLt
    have h_meas_t : Measurable (fun (traj : Phase2.Trajectory (Fin 2) Bool T) => (traj t).1) := Phase2.measurable_traj_action t.val t.isLt
    have h_meas_t1 : Measurable (fun (traj' : Phase2.Trajectory (Fin 2) Bool (t.val + 1)) => (traj' ⟨t.val, Nat.lt_succ_self _⟩).1) := Phase2.measurable_traj_action t.val (Nat.lt_succ_self _)
    have h_meas_set : MeasurableSet ((fun (traj' : Phase2.Trajectory (Fin 2) Bool (t.val + 1)) => (traj' ⟨t.val, Nat.lt_succ_self _⟩).1) ⁻¹' {0}) :=
      h_meas_t1 (measurableSet_singleton 0)
    have h_trunc := Phase2.trajMeasure_truncation (env₆_nonstat T Δ hΔ0 hΔ4) alg (env₆_nonstat T Δ hΔ0 hΔ4).hr_meas hEnv hAlg T (t.val + 1) ht_le _ h_meas_set
    have h_set_eq : {traj' : Phase2.Trajectory (Fin 2) Bool T | (traj' t).1 = 0} =
        {traj : Phase2.Trajectory (Fin 2) Bool T | (fun (i : Fin (t.val + 1)) => traj (Fin.castLE ht_le i)) ∈ (fun (traj' : Phase2.Trajectory (Fin 2) Bool (t.val + 1)) => (traj' ⟨t.val, Nat.lt_succ_self _⟩).1) ⁻¹' {0}} := by
      ext traj
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
      rfl
    rw [h_set_eq, h_trunc]
    dsimp [Phase2.actionMarginal]
    rw [Measure.map_apply h_meas_t1 (measurableSet_singleton 0)]
  have h_marg1_eq : (Phase2.trajMeasure (env₆_nonstat T Δ hΔ0 hΔ4) alg (env₆_nonstat T Δ hΔ0 hΔ4).hr_meas T {traj' | (traj' t).1 = 1}).toReal =
    (Phase2.actionMarginal (env₆_nonstat T Δ hΔ0 hΔ4) alg (env₆_nonstat T Δ hΔ0 hΔ4).hr_meas hEnv hAlg (t.val + 1) ⟨t.val, Nat.lt_succ_self _⟩ {1}).toReal := by
    have ht_le : t.val + 1 ≤ T := t.isLt
    have h_meas_t : Measurable (fun (traj : Phase2.Trajectory (Fin 2) Bool T) => (traj t).1) := Phase2.measurable_traj_action t.val t.isLt
    have h_meas_t1 : Measurable (fun (traj' : Phase2.Trajectory (Fin 2) Bool (t.val + 1)) => (traj' ⟨t.val, Nat.lt_succ_self _⟩).1) := Phase2.measurable_traj_action t.val (Nat.lt_succ_self _)
    have h_meas_set : MeasurableSet ((fun (traj' : Phase2.Trajectory (Fin 2) Bool (t.val + 1)) => (traj' ⟨t.val, Nat.lt_succ_self _⟩).1) ⁻¹' {1}) :=
      h_meas_t1 (measurableSet_singleton 1)
    have h_trunc := Phase2.trajMeasure_truncation (env₆_nonstat T Δ hΔ0 hΔ4) alg (env₆_nonstat T Δ hΔ0 hΔ4).hr_meas hEnv hAlg T (t.val + 1) ht_le _ h_meas_set
    have h_set_eq : {traj' : Phase2.Trajectory (Fin 2) Bool T | (traj' t).1 = 1} =
        {traj : Phase2.Trajectory (Fin 2) Bool T | (fun (i : Fin (t.val + 1)) => traj (Fin.castLE ht_le i)) ∈ (fun (traj' : Phase2.Trajectory (Fin 2) Bool (t.val + 1)) => (traj' ⟨t.val, Nat.lt_succ_self _⟩).1) ⁻¹' {1}} := by
      ext traj
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
      rfl
    rw [h_set_eq, h_trunc]
    dsimp [Phase2.actionMarginal]
    rw [Measure.map_apply h_meas_t1 (measurableSet_singleton 1)]
  rw [h_marg0_eq, h_marg1_eq]
  set p1 := (Phase2.actionMarginal (env₆_nonstat T Δ hΔ0 hΔ4) alg (env₆_nonstat T Δ hΔ0 hΔ4).hr_meas hEnv hAlg (t.val + 1) ⟨t.val, Nat.lt_succ_self _⟩ {1}).toReal
  set p0 := (Phase2.actionMarginal (env₆_nonstat T Δ hΔ0 hΔ4) alg (env₆_nonstat T Δ hΔ0 hΔ4).hr_meas hEnv hAlg (t.val + 1) ⟨t.val, Nat.lt_succ_self _⟩ {0}).toReal
  haveI hμ_prob : IsProbabilityMeasure (Phase2.actionMarginal (env₆_nonstat T Δ hΔ0 hΔ4) alg (env₆_nonstat T Δ hΔ0 hΔ4).hr_meas hEnv hAlg (t.val + 1) ⟨t.val, Nat.lt_succ_self _⟩) := Phase2.actionMarginal_isProbability _ _ _ _ _ _ _
  have h_sum_μ : p0 + p1 = 1 := by
    have h_disj : Disjoint ({0} : Set (Fin 2)) ({1} : Set (Fin 2)) := Set.disjoint_singleton.mpr (by decide)
    have h_union : ({0} : Set (Fin 2)) ∪ {1} = Set.univ := by ext x; fin_cases x <;> decide
    have h_meas_eq : (Phase2.actionMarginal (env₆_nonstat T Δ hΔ0 hΔ4) alg (env₆_nonstat T Δ hΔ0 hΔ4).hr_meas hEnv hAlg (t.val + 1) ⟨t.val, Nat.lt_succ_self _⟩) ({0} ∪ {1}) =
                     (Phase2.actionMarginal (env₆_nonstat T Δ hΔ0 hΔ4) alg (env₆_nonstat T Δ hΔ0 hΔ4).hr_meas hEnv hAlg (t.val + 1) ⟨t.val, Nat.lt_succ_self _⟩) {0} +
                     (Phase2.actionMarginal (env₆_nonstat T Δ hΔ0 hΔ4) alg (env₆_nonstat T Δ hΔ0 hΔ4).hr_meas hEnv hAlg (t.val + 1) ⟨t.val, Nat.lt_succ_self _⟩) {1} := measure_union h_disj (measurableSet_singleton 1)
    rw [h_union, measure_univ] at h_meas_eq
    have h_toReal : p0 + p1 = (1 : ENNReal).toReal := by
      change ((Phase2.actionMarginal (env₆_nonstat T Δ hΔ0 hΔ4) alg (env₆_nonstat T Δ hΔ0 hΔ4).hr_meas hEnv hAlg (t.val + 1) ⟨t.val, Nat.lt_succ_self _⟩) {0}).toReal +
             ((Phase2.actionMarginal (env₆_nonstat T Δ hΔ0 hΔ4) alg (env₆_nonstat T Δ hΔ0 hΔ4).hr_meas hEnv hAlg (t.val + 1) ⟨t.val, Nat.lt_succ_self _⟩) {1}).toReal = _
      rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
      rw [← h_meas_eq]
    rw [ENNReal.toReal_one] at h_toReal
    exact h_toReal
  have hp0_eq : p0 = 1 - p1 := by linarith
  rw [hp0_eq]
  have h_alg : (1 / 2 + Δ) * (1 - p1) + (1 / 2 - Δ) * p1 = 1 / 2 + Δ - 2 * Δ * p1 := by ring
  rw [h_alg]
  have h_bound : 1 / 2 + Δ - 2 * Δ * p1 ≤ 1 / 2 - 2 * δ * Δ := by
    have h2D : 0 ≤ 2 * Δ := by linarith
    have hp1_bound : 2 * Δ * (1 / 2 + δ) ≤ 2 * Δ * p1 := mul_le_mul_of_nonneg_left h_stale h2D
    linarith
  exact h_bound

theorem necessity_x6_explicit_bound
    {Sig : Type} [MeasurableSpace Sig] [TopologicalSpace Sig] [BorelSpace Sig]
    [MeasurableSingletonClass Sig] [MeasurableEq Sig]
    (T : ℕ)
    (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ4 : Δ ≤ 1 / 4)
    (ε : ℝ) (hε0 : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (δ : ℝ) (hδ : 0 < δ)
    (tau : ℕ) (htau : tau = T / 2)
    (alg : SixPrimitives.Algorithm (Fin 2) Bool Sig)
    (hAlg : Phase2.AlgIsMarkov alg)
    (hLacks_post : ∀ t : ℕ, tau < t → t ≤ Nat.floor ((1 + ε) * (tau : ℝ)) →
      (Phase2.staleProbSeq (env₆_nonstat T Δ hΔ0 hΔ4) alg
        (env₆_nonstat T Δ hΔ0 hΔ4).hr_meas 1 t) ≥ 1 / 2 + δ) :
    Δ * (1 + 2 * δ) * ((ε / 2) * (T : ℝ) - (ε / 2 + 1)) ≤
      SixPrimitives.regret (env₆_nonstat T Δ hΔ0 hΔ4) alg T := by
  haveI := hAlg.act_markov
  haveI := hAlg.update_markov
  by_cases hT0 : T = 0
  · subst hT0
    have h_r_bound : ∀ s a, |(env₆_nonstat 0 Δ hΔ0 hΔ4).r (s, a)| ≤ 1 := by
      intro s a
      dsimp [env₆_nonstat]
      split_ifs
      · rw [abs_of_pos (by linarith)]
        linarith
      · rw [abs_of_pos (by linarith)]
        linarith
    have h_reg_nonneg : 0 ≤ SixPrimitives.regret (env₆_nonstat 0 Δ hΔ0 hΔ4) alg 0 :=
      Phase2.regret_nonneg (env₆_nonstat 0 Δ hΔ0 hΔ4) alg (env₆_nonstat_isMarkov 0 Δ hΔ0 hΔ4) 0 h_r_bound
    have h_lhs_neg : Δ * (1 + 2 * δ) * ((ε / 2) * ((0 : ℕ) : ℝ) - (ε / 2 + 1)) ≤ 0 := by
      have h1 : 0 ≤ Δ * (1 + 2 * δ) := by positivity
      have h2 : (ε / 2) * ((0 : ℕ) : ℝ) - (ε / 2 + 1) ≤ 0 := by
        simp only [Nat.cast_zero, mul_zero, zero_sub]
        linarith
      exact mul_nonpos_of_nonneg_of_nonpos h1 h2
    calc Δ * (1 + 2 * δ) * ((ε / 2) * ((0 : ℕ) : ℝ) - (ε / 2 + 1))
      _ ≤ 0 := h_lhs_neg
      _ ≤ SixPrimitives.regret (env₆_nonstat 0 Δ hΔ0 hΔ4) alg 0 := h_reg_nonneg
  · have hT_pos : 0 < T := Nat.pos_of_ne_zero hT0
    let env := env₆_nonstat T Δ hΔ0 hΔ4
    have hEnv := env₆_nonstat_isMarkov T Δ hΔ0 hΔ4
    have h_opt : SixPrimitives.optValue env T = (1 / 2 + Δ) * (T : ℝ) := env₆_optValue T Δ hΔ0 hΔ4
    unfold SixPrimitives.regret
    rw [h_opt]
    rw [Phase2.algValue_eq_algValue']
    have h_r_bound : ∀ s a, |env.r (s, a)| ≤ 1 / 2 + Δ := by
      intro s a
      change |(env₆_nonstat T Δ hΔ0 hΔ4).r (s, a)| ≤ 1 / 2 + Δ
      dsimp [env₆_nonstat]
      split_ifs
      · rw [abs_of_pos (by linarith)]
      · rw [abs_of_pos (by linarith)]
        linarith
    rw [Phase2.algValue'_eq_sum env alg env.hr_meas hEnv hAlg h_r_bound T]
    have h_T_mul : (1 / 2 + Δ) * (T : ℝ) = ∑ _t : Fin T, (1 / 2 + Δ) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    rw [h_T_mul, ← Finset.sum_sub_distrib]
    let E_R := fun (t : Fin T) => ∫ traj : Phase2.Trajectory (Fin 2) Bool T, (traj t).2.2 ∂Phase2.trajMeasure env alg env.hr_meas T
    have h_nonneg : ∀ t : Fin T, 0 ≤ 1 / 2 + Δ - E_R t := by
      intro t
      have h_le := env₆_step_reward_le_opt T Δ hΔ0 hΔ4 alg hAlg t
      exact sub_nonneg.mpr h_le
    have h_sum_fin : ∑ t : Fin T, (1 / 2 + Δ - E_R t) = ∑ i ∈ Finset.range T, (if h : i < T then 1 / 2 + Δ - E_R ⟨i, h⟩ else 0) := by
      rw [Finset.sum_fin_eq_sum_range]
    let M := Nat.floor ((1 + ε) * (tau : ℝ))
    have h_M_lt_T : M < T := by
      have h_eps_bound : 1 + ε ≤ 3 / 2 := by linarith
      have h_tau_bound : (tau : ℝ) ≤ (T : ℝ) / 2 := by
        rw [htau]
        have hT_mod : T % 2 = 0 ∨ T % 2 = 1 := by omega
        rcases hT_mod with h0 | h1
        · have : 2 * (T / 2) = T := by omega
          have hr : 2 * ((T / 2 : ℕ) : ℝ) = (T : ℝ) := by exact_mod_cast this
          linarith
        · have : 2 * (T / 2) + 1 = T := by omega
          have hr : 2 * ((T / 2 : ℕ) : ℝ) + 1 = (T : ℝ) := by exact_mod_cast this
          linarith
      have h_mul_bound : (1 + ε) * (tau : ℝ) ≤ (3 / 2) * ((T : ℝ) / 2) :=
        mul_le_mul h_eps_bound h_tau_bound (Nat.cast_nonneg _) (by norm_num)
      have h_mul_eval : (3 / 2) * ((T : ℝ) / 2) = (3 / 4) * (T : ℝ) := by ring
      have h_strict : (3 / 4) * (T : ℝ) < (T : ℝ) := by
        have hT_pos_real : 0 < (T : ℝ) := Nat.cast_pos.mpr hT_pos
        linarith
      have h_combined : (1 + ε) * (tau : ℝ) < (T : ℝ) := by linarith
      have h_M_real : (M : ℝ) ≤ (1 + ε) * (tau : ℝ) := Nat.floor_le (by positivity)
      have h_M_lt_T_real : (M : ℝ) < (T : ℝ) := by linarith
      exact_mod_cast h_M_lt_T_real
    have h_subset : Finset.Ioc tau M ⊆ Finset.range T := by
      intro x hx
      rw [Finset.mem_Ioc] at hx
      rw [Finset.mem_range]
      omega
    have h_subset_sum : ∑ i ∈ Finset.Ioc tau M, (if h : i < T then 1 / 2 + Δ - E_R ⟨i, h⟩ else 0) ≤ ∑ i ∈ Finset.range T, (if h : i < T then 1 / 2 + Δ - E_R ⟨i, h⟩ else 0) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg h_subset
      intro i _ _
      split_ifs
      · exact h_nonneg _
      · rfl
    have h_term_lb : ∀ i ∈ Finset.Ioc tau M, Δ * (1 + 2 * δ) ≤ (if h : i < T then 1 / 2 + Δ - E_R ⟨i, h⟩ else 0) := by
      intro i hi
      rw [Finset.mem_Ioc] at hi
      have hi_lt_T : i < T := by omega
      rw [dif_pos hi_lt_T]
      have h_post : tau < i := hi.1
      have h_M : i ≤ M := hi.2
      have h_stale_cond := hLacks_post i h_post h_M
      rw [staleProbSeq_eq_actionMarginal T Δ hΔ0 hΔ4 alg hAlg i] at h_stale_cond
      have h_post_cp : T / 2 < (⟨i, hi_lt_T⟩ : Fin T).val := by
        change T / 2 < i
        omega
      have h_rew_bound := env₆_post_cp_reward_bound T Δ hΔ0 hΔ4 alg hAlg ⟨i, hi_lt_T⟩ h_post_cp δ hδ h_stale_cond
      change Δ * (1 + 2 * δ) ≤ 1 / 2 + Δ - ∫ traj : Phase2.Trajectory (Fin 2) Bool T, (traj ⟨i, hi_lt_T⟩).2.2 ∂Phase2.trajMeasure env alg env.hr_meas T
      linarith
    have h_sum_lb : ∑ i ∈ Finset.Ioc tau M, Δ * (1 + 2 * δ) ≤ ∑ i ∈ Finset.Ioc tau M, (if h : i < T then 1 / 2 + Δ - E_R ⟨i, h⟩ else 0) :=
      Finset.sum_le_sum h_term_lb
    have h_sum_eval : ∑ i ∈ Finset.Ioc tau M, Δ * (1 + 2 * δ) = (M - tau : ℝ) * (Δ * (1 + 2 * δ)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      have h_card : ((Finset.Ioc tau M).card : ℝ) = (M - tau : ℝ) := by
        have h_tau_le_M : tau ≤ M := by
          apply Nat.le_floor
          calc (tau : ℝ) = 1 * (tau : ℝ) := by ring
            _ ≤ (1 + ε) * (tau : ℝ) := mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
        rw [Nat.card_Ioc, Nat.cast_sub h_tau_le_M]
      rw [h_card]
    have h_win_lb := window_length_lower_bound T ε hε0 tau htau
    have h_delta_pos : 0 ≤ Δ * (1 + 2 * δ) := by positivity
    have h_final_lb : Δ * (1 + 2 * δ) * ((ε / 2) * (T : ℝ) - (ε / 2 + 1)) ≤ (M - tau : ℝ) * (Δ * (1 + 2 * δ)) := by
      calc Δ * (1 + 2 * δ) * ((ε / 2) * (T : ℝ) - (ε / 2 + 1))
        _ = ((ε / 2) * (T : ℝ) - (ε / 2 + 1)) * (Δ * (1 + 2 * δ)) := mul_comm _ _
        _ ≤ (M - tau : ℝ) * (Δ * (1 + 2 * δ)) := mul_le_mul_of_nonneg_right h_win_lb h_delta_pos
    rw [h_sum_fin]
    calc Δ * (1 + 2 * δ) * ((ε / 2) * (T : ℝ) - (ε / 2 + 1))
      _ ≤ (M - tau : ℝ) * (Δ * (1 + 2 * δ)) := h_final_lb
      _ = ∑ i ∈ Finset.Ioc tau M, Δ * (1 + 2 * δ) := h_sum_eval.symm
      _ ≤ ∑ i ∈ Finset.Ioc tau M, (if h : i < T then 1 / 2 + Δ - E_R ⟨i, h⟩ else 0) := h_sum_lb
      _ ≤ ∑ i ∈ Finset.range T, (if h : i < T then 1 / 2 + Δ - E_R ⟨i, h⟩ else 0) := h_subset_sum

theorem necessity_x6
    {Sig : Type} [MeasurableSpace Sig] [TopologicalSpace Sig] [BorelSpace Sig]
    [MeasurableSingletonClass Sig] [MeasurableEq Sig]
    (T : ℕ)
    (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ4 : Δ ≤ 1 / 4)
    (ε : ℝ) (hε0 : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (δ : ℝ) (hδ : 0 < δ)
    (tau : ℕ) (htau : tau = T / 2)
    (alg : SixPrimitives.Algorithm (Fin 2) Bool Sig)
    (hAlg : Phase2.AlgIsMarkov alg)
    (hLacks_post : ∀ t : ℕ, tau < t → t ≤ Nat.floor ((1 + ε) * (tau : ℝ)) →
      (Phase2.staleProbSeq (env₆_nonstat T Δ hΔ0 hΔ4) alg
        (env₆_nonstat T Δ hΔ0 hΔ4).hr_meas 1 t) ≥ 1 / 2 + δ) :
    ∃ c > 0, ∃ d : ℝ, c * (T : ℝ) - d ≤ SixPrimitives.regret (env₆_nonstat T Δ hΔ0 hΔ4) alg T := by
  use Δ * (1 + 2 * δ) * (ε / 2)
  constructor
  · positivity
  · use Δ * (1 + 2 * δ) * (ε / 2 + 1)
    have h_bound := necessity_x6_explicit_bound T Δ hΔ0 hΔ4 ε hε0 hε2 δ hδ tau htau alg hAlg hLacks_post
    calc Δ * (1 + 2 * δ) * (ε / 2) * (T : ℝ) - Δ * (1 + 2 * δ) * (ε / 2 + 1)
      _ = Δ * (1 + 2 * δ) * ((ε / 2) * (T : ℝ) - (ε / 2 + 1)) := by ring
      _ ≤ SixPrimitives.regret (env₆_nonstat T Δ hΔ0 hΔ4) alg T := h_bound

end NecessityX6

end SixPrimitives
