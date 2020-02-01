(*
  File:    Harmonic_Numbers_Are_Not_Integers.thy 
  Author:  Jose Manuel Rodriguez Caballero, University of Tartu
*)
section \<open>Harmonic numbers are not integers, except for the trivial case of 1\<close>
theory Harmonic_Numbers_Are_Not_Integers

imports 
  Complex_Main 
  "HOL-Algebra.Exponent"
  "HOL-ex.Sketch_and_Explore"

begin

text \<open>
 In 1915, L. Theisinger ~\cite{theisinger1915bemerkung} proved that, except for the trivial 
 case of 1, the harmonic numbers are not integers. We formalize this result as 
 theorem Harmonic_Numbers_Are_Not_Integers.
\<close>

subsection \<open>Multiplicity\<close>

text \<open> multipl' p n = multiplicitly (p+2) (n+1) \<close>

lemma multipl'_rec: 
  fixes n::nat and p::nat
  assumes \<open>n \<noteq> 0\<close>
  shows \<open>(((n+1) div (p+2)))-1 < n\<close>
  by (smt add.commute add_diff_inverse_nat add_less_same_cancel2 assms div_less_dividend less_one linorder_neqE_nat nat_add_left_cancel_less not_add_less2 one_less_numeral_iff semiring_norm(76) zero_less_diff)
  
function multipl' :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  where
    "multipl' p 0 = 0"
  | "p+2 dvd n+1 \<Longrightarrow> multipl' p n = Suc (multipl' p (((n+1) div (p+2)))-1)"
  | "\<not> (p+2 dvd n+1) \<Longrightarrow>  multipl' p n = 0"
        apply simp+
        apply (metis old.prod.exhaust)
       apply metis
      apply (metis Suc_1 Suc_eq_plus1 Suc_le_mono Suc_n_not_le_n add_Suc_right divides_aux_eq dvd_1_left
      dvd_antisym le0)
     apply metis
    apply (metis old.prod.inject)
   apply (metis prod.inject)
  by metis
termination 
  apply auto
  proof
  show "multipl'_dom y"
    if "multipl'_rel y (a, b)"
    for a :: nat
      and b :: nat
      and y :: "nat \<times> nat"
    using that sorry
qed

fun multipl :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
\<open>multipl p n = multipl' (p-2) (n-1)\<close>

lemma multipl_multiplicity:
  fixes p::nat and n::nat
  assumes \<open>prime p\<close> and \<open>n \<noteq> 0\<close>
  shows \<open>multipl p n = multiplicity p n\<close>
  sorry

(*
value \<open>multipl 2 12\<close>


value \<open>multipl 2 ( nat (snd (quotient_of (Fract 2 4))) )\<close>
*)


subsection \<open>Auxiliary results\<close>


subsection \<open>Main result\<close>

theorem Harmonic_Numbers_Are_Not_Integers:
  fixes n :: nat
  assumes \<open>n \<ge> 2\<close>
  shows \<open>(\<Sum> k = 1..n. (Fract 1 (of_nat k)) ) \<notin> \<int>\<close>
  sorry

end

