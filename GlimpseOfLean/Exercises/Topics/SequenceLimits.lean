import GlimpseOfLean.Library.Basic

/-
In this file we manipulate the elementary definition of limits of
sequences of real numbers.
mathlib has a much more general definition of limits, but here
we want to practice using the logical operators and relations
covered in the previous files.
-/

/-
Before we start on, let us make sure Lean doesn't need so much help to
prove equalities or inequalities that linearly follow from known
equalities and inequalities. This is the job of the linear arithmetic
tactic: `linarith`.
-/

example (a b : ℝ) (hb : 0 ≤ b) : a ≤ a + b := by linarith

/-
Let's prove some exercises using `linarith`.
-/

example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a + b := by linarith

example (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d) : a + c ≤ b + d := by linarith

/-
A sequence `u` is a function from `ℕ` to `ℝ`, hence Lean says
`u : ℕ → ℝ`
The definition we'll be using is:

-- Definition of « u tends to l »
`def seq_limit (u : ℕ → ℝ) (l : ℝ) := ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε`

Note the use of `∀ ε > 0, _` which is an abbreviation of
`∀ ε, ε > 0 → _ `

In particular, a statement like `h : ∀ ε > 0, _`
can be specialized to a given `ε₀` by
  `specialize h ε₀ hε₀`
where `hε₀` is a proof of `ε₀ > 0`.

Also note that, wherever Lean expects some proof term, we can
start a tactic mode proof using the keyword `by`.
For instance, if the local context contains:

δ : ℝ
δ_pos : δ > 0
h : ∀ ε > 0, _

then we can specialize h to the real number δ/2 using:
  `specialize h (δ/2) (by linarith)`
where `by linarith` will provide the proof of `δ/2 > 0` expected by Lean.
-/

/- If u is constant with value l then u tends to l.
Hint: `simp` can rewrite `|1 - 1|` to `0` -/
example (h : ∀ n, u n = l) : seq_limit u l := by {
  intro ε _
  use 0
  intro n _
  calc
    |u n - l| = |l - l| := by rw [h n]
            _ = 0       := by simp
            _ ≤ ε       := by linarith
}


/- When dealing with absolute values, we'll use lemmas:

`abs_sub_comm (x y : ℝ) : |x - y| = |y - x|`

`abs_le {x y : ℝ} : |x| ≤ y ↔ -y ≤ x ∧ x ≤ y`

We will also use variants of the triangle inequality

`abs_add (x y : ℝ) : |x + y| ≤ |x| + |y|`
or
`abs_sub_le  (a c b : ℝ) : |a - b| ≤ |a - c| + |c - b|`
or the primed version:
`abs_sub_le' (a c b : ℝ) : |a - b| ≤ |a - c| + |b - c|`
-/

-- Assume `l > 0`. Then `u` ts to `l` implies `u n ≥ l/2` for large enough `n`
example (h : seq_limit u l) (hl : l > 0) :
    ∃ N, ∀ n ≥ N, u n ≥ l/2 := by {
  rcases h (l/2) (by linarith) with ⟨ep, hep⟩
  use ep
  intro n hn
  specialize hep n hn
  rw [abs_le] at hep
  linarith
}


/-
When dealing with max, you can use

`ge_max_iff (p q r) : r ≥ max p q ↔ r ≥ p ∧ r ≥ q`

`le_max_left p q : p ≤ max p q`

`le_max_right p q : q ≤ max p q`

Let's see an example.
-/

-- If `u` tends to `l` and `v` tends `l'` then `u+v` tends to `l+l'`
example (hu : seq_limit u l) (hv : seq_limit v l') :
    seq_limit (u + v) (l + l') := by {
  intros ε ε_pos
  rcases hu (ε/2) (by linarith) with ⟨N₁, hN₁⟩
  rcases hv (ε/2) (by linarith) with ⟨N₂, hN₂⟩
  use max N₁ N₂
  intros n hn
  rw [ge_max_iff] at hn
  rcases hn with ⟨hn₁, hn₂⟩
  have fact₁ : |u n - l| ≤ ε/2 := hN₁ n hn₁
  have fact₂ : |v n - l'| ≤ ε/2 := hN₂ n hn₂
  calc
    |(u + v) n - (l + l')| = |u n + v n - (l + l')|   := by rfl
                         _ = |(u n - l) + (v n - l')| := by ring
                         _ ≤ |u n - l| + |v n - l'|   := by apply abs_add
                         _ ≤ ε                        := by linarith [fact₁, fact₂]
}


/- Let's do something similar: the squeezing theorem. -/
example (hu : seq_limit u l) (hw : seq_limit w l) (h : ∀ n, u n ≤ v n) (h' : ∀ n, v n ≤ w n) :
    seq_limit v l := by {
  intro ε ε_pos
  rcases hu ε ε_pos with ⟨Nu, hu⟩
  rcases hw ε ε_pos with ⟨Nw, hw⟩
  use max Nu Nw
  intro n hn
  rw [ge_max_iff] at hn; rcases hn with ⟨hn₁, hn₂⟩
  rw [abs_le]
  constructor
  · specialize hu n hn₁
    rw [abs_le] at hu
    calc
      -ε ≤ u n - l := by exact hu.1
       _ ≤ v n - l := by exact tsub_le_tsub_right (h n) l
  · specialize hw n hn₂
    rw [abs_le] at hw
    calc
      v n - l ≤ w n - l := by exact tsub_le_tsub_right (h' n) l
             _ ≤ ε      := by exact hw.2
}



/- In the next exercise, we'll use

`eq_of_abs_sub_le_all (x y : ℝ) : (∀ ε > 0, |x - y| ≤ ε) → x = y`

Recall we listed three variations on the triangle inequality at the beginning of this file.
-/

-- A sequence admits at most one limit. You will be able to use that lemma in the following
-- exercises.
lemma uniq_limit : seq_limit u l → seq_limit u l' → l = l' := by {
  intros hl hl'
  apply eq_of_abs_sub_le_all
  intro ε ε_pos
  rcases hl (ε/2) (by linarith) with ⟨N₁, hl⟩
  rcases hl' (ε/2) (by linarith) with ⟨N₂, hl'⟩
  let n := max N₁ N₂
  specialize hl n (le_max_left N₁ N₂)
  specialize hl' n (le_max_right N₁ N₂)
  calc
    |l-l'| ≤ |l - (u n)| + |(u n) - l'| := by exact abs_sub_le l (u n) l'
         _ = |(u n) - l| + |(u n) - l'| := by rw [abs_sub_comm]
         _ ≤ ε/2 + ε/2                  := by linarith [hl, hl']
         _ = ε                          := by ring
}



/-
Let's now practice deciphering definitions before proving.
-/

def non_decreasing (u : ℕ → ℝ) := ∀ n m, n ≤ m → u n ≤ u m

def is_seq_sup (M : ℝ) (u : ℕ → ℝ) :=
(∀ n, u n ≤ M) ∧ ∀ ε > 0, ∃ n₀, u n₀ ≥ M - ε

example (M : ℝ) (h : is_seq_sup M u) (h' : non_decreasing u) : seq_limit u M := by {
  intro ε ε_pos
  rcases h with ⟨M_max, M_reach⟩
  rcases M_reach ε ε_pos with ⟨n₀,hn₀⟩
  use n₀
  intro n hn
  rw [abs_le]
  constructor
  · calc
      -ε ≤ u n₀ - M := by exact le_tsub_of_add_le_left hn₀
       _ ≤ u n - M  := by exact tsub_le_tsub_right (h' n₀ n hn) M
  · calc
      u n - M ≤ M - M := by exact tsub_le_tsub_right (M_max n) M
            _ = 0     := by ring
            _ ≤ ε     := by exact le_of_lt ε_pos
}

/-
We will now play with subsequences.

The new definition we will use is that `φ : ℕ → ℕ` is an extraction
if it is (strictly) increasing.

`def extraction (φ : ℕ → ℕ) := ∀ n m, n < m → φ n < φ m`

In the following, `φ` will always denote a function from `ℕ` to `ℕ`.

The next lemma is proved by an easy induction, but we haven't seen induction
in this tutorial. If you did the natural number game then you can delete
the proof below and try to reconstruct it.
-/
/-- An extraction is greater than id -/
lemma id_le_extraction' : extraction φ → ∀ n, n ≤ φ n := by {
  intros hyp n
  induction n with
  | zero => exact zero_le _
  | succ n ih => exact Nat.succ_le_of_lt (by linarith [hyp n (n+1) (by linarith)])
}


/-
In the exercise, we use `∃ n ≥ N, ...` which is the abbreviation of
`∃ n, n ≥ N ∧ ...`.
-/

/-- Extractions take arbitrarily large values for arbitrarily large
inputs. -/
lemma extraction_ge : extraction φ → ∀ N N', ∃ n ≥ N', φ n ≥ N := by {
  intros hyp N N'
  unfold extraction at hyp
  let n := max N N' + 1
  use n
  have n_gt_N : n > N := by calc 
    n  > max N N'     := by linarith
    _ ≥ N             := by exact le_max_left N N'
  constructor
  · linarith [le_max_right N N']
  · calc
      φ n ≥ φ N := by linarith [hyp N n n_gt_N]
      /- φ n ≥ φ (max N N') := by exact Nat.le_of_succ_le (hyp N n n_gt_N) -/
      /-   _ ≥ φ N := by exact Nat.le_of_succ_le (hyp N n n_gt_N) -/
        _ ≥ N   := by exact id_le_extraction' hyp N

}

/- A real number `a` is a cluster point of a sequence `u`
if `u` has a subsequence converging to `a`.

`def cluster_point (u : ℕ → ℝ) (a : ℝ) := ∃ φ, extraction φ ∧ seq_limit (u ∘ φ) a`
-/


/-- If `a` is a cluster point of `u` then there are values of
`u` arbitrarily close to `a` for arbitrarily large input. -/
lemma near_cluster :
  cluster_point u a → ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| ≤ ε := by {
  intros cluster ε ε_pos N₁
  
  rcases cluster with ⟨φ, hyp, seql⟩
  rcases seql ε ε_pos with ⟨N₂, seql⟩
  let N := max N₁ N₂

  have φn_ge_N₁ := ge_trans (id_le_extraction' hyp N) (le_max_left N₁ N₂)
  use φ N
  constructor
  · exact φn_ge_N₁
  · exact seql N (by exact le_max_right N₁ N₂)
}


/-- If `u` tends to `l` then its subsequences tend to `l`. -/
lemma subseq_tendsto_of_tendsto' (h : seq_limit u l) (hφ : extraction φ) :
seq_limit (u ∘ φ) l := by {
  intro ε ε_pos
  rcases h ε ε_pos with ⟨N, h⟩
  use N
  intro n hn

  have φn_ge_N := ge_trans (id_le_extraction' hφ n) hn
  exact h (φ n) φn_ge_N
}

/-- If `u` tends to `l` all its cluster points are equal to `l`. -/
lemma cluster_limit (hl : seq_limit u l) (ha : cluster_point u a) : a = l := by {
  apply near_cluster at ha
  apply eq_of_abs_sub_le_all
  intro ε ε_pos

  rcases hl (ε/2) (by linarith) with ⟨N₂, hl⟩

  specialize ha (ε/2) (by linarith) N₂
  rcases ha with ⟨n, n_ge_N₂, ha⟩

  calc
    |a - l| ≤ |a - u n| + |u n - l| := by exact abs_sub_le a (u n) l
          _ = |u n - a| + |u n - l| := by rw [abs_sub_comm]
          _ ≤ |u n - a| + ε / 2     := by linarith [hl n n_ge_N₂]
          _ ≤ ε / 2 + ε / 2         := by linarith [ha]
          _ = ε := by ring
}

/-- Cauchy_sequence sequence -/
def CauchySequence (u : ℕ → ℝ) :=
  ∀ ε > 0, ∃ N, ∀ p q, p ≥ N → q ≥ N → |u p - u q| ≤ ε

example : (∃ l, seq_limit u l) → CauchySequence u := by {
  intros lim ε ε_pos
  rcases lim with ⟨l, l_lim⟩
  rcases l_lim (ε/2) (by linarith) with ⟨N, l_lim⟩
  use N
  intros p q p_ge_N q_ge_N
  calc
    |u p - u q| ≤ |u p - l| + |u q - l| := by exact abs_sub_le' (u p) l (u q)
              _ ≤ |u p - l| + ε / 2     := by linarith [l_lim q q_ge_N]
              _ ≤ ε / 2     + ε / 2     := by linarith [l_lim p p_ge_N]
              _ = ε                     := by ring
}

/-
In the next exercise, you can reuse
 near_cluster : cluster_point u a → ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| ≤ ε
-/

example (hu : CauchySequence u) (hl : cluster_point u l) : seq_limit u l := by {
  intros ε ε_pos

  apply near_cluster at hl

  rcases hu (ε/2) (by linarith) with ⟨N₁, hu⟩
  rcases hl (ε/2) (by linarith) N₁ with ⟨N₂, N₂_ge_N₁, hseql⟩

  use N₁
  intro n n_ge_N₁

  calc
    |u n - l| ≤ |u n - u N₂| + |u N₂ - l| := by exact abs_sub_le (u n) (u N₂) l
            _ ≤ |u n - u N₂| + ε / 2      := by linarith [hseql]
            _ ≤ ε / 2        + ε / 2      := by linarith [hu n N₂ n_ge_N₁ N₂_ge_N₁]
            _ = ε                         := by ring
}
