(*
  File:    Harmonic_Numbers_Are_Not_Integers.thy 
  Author:  Jose Manuel Rodriguez Caballero, University of Tartu
*)
section \<open>Harmonic numbers are not integers, except for the trivial case of 1\<close>
theory Harmonic_Numbers_Are_Not_Integers

imports 
  Complex_Main 
  "HOL-ex.Sketch_and_Explore"
  "Probabilistic_Prime_Tests.Fermat_Witness"

begin

text \<open>
 In 1915, L. Theisinger ~\cite{theisinger1915bemerkung} proved that, except for the trivial 
 case of 1, the harmonic numbers are not integers. We formalize this result as 
 theorem @{text harmonic_numbers_are_not_integers}.
\<close>

subsection \<open>p-adic norm\<close>

text\<open>
  The following function is a version of the p-adic valuation, with the exception that for
  us the valuation of zero will be zero rather than infinite as in done in traditional mathematics.
\<close>
definition pval :: \<open>nat \<Rightarrow> rat \<Rightarrow> int\<close> where
  \<open>pval p x = int (multiplicity p  (fst (quotient_of x)) ) - 
                   int (multiplicity p  (snd (quotient_of x)) )\<close>

lemma integers_pval_I:
  \<open>(\<And> p. prime p \<Longrightarrow> pval p x \<ge> 0) \<Longrightarrow> x \<in> \<int>\<close>
proof-
  assume \<open>\<And> p. prime p \<Longrightarrow> pval p x \<ge> 0\<close>
  have \<open>prime p \<Longrightarrow> multiplicity p (snd (quotient_of x)) = 0\<close>
    for p::nat
  proof-
    assume \<open>prime p\<close>
    hence \<open>pval p x \<ge> 0\<close>
      by (simp add: \<open>\<And>p. prime p \<Longrightarrow> 0 \<le> pval p x\<close>)
    hence \<open>multiplicity p (fst (quotient_of x)) \<ge> multiplicity p (snd (quotient_of x))\<close>
      using pval_def 
      by auto
    show ?thesis
    proof(rule classical)
      assume \<open>\<not>(multiplicity p (snd (quotient_of x)) = 0)\<close>
      hence \<open>multiplicity p (snd (quotient_of x)) \<ge> 1\<close>
        by simp
      hence \<open>multiplicity p (fst (quotient_of x)) \<ge> 1\<close>
        using \<open>multiplicity p (fst (quotient_of x)) \<ge> multiplicity p (snd (quotient_of x))\<close>
        by auto
      hence \<open>p dvd fst (quotient_of x)\<close>
        using not_dvd_imp_multiplicity_0 
        by fastforce
      moreover have \<open>p dvd snd (quotient_of x)\<close>
        by (meson \<open>multiplicity (int p) (snd (quotient_of x)) \<noteq> 0\<close> not_dvd_imp_multiplicity_0)
      ultimately have \<open>\<not> coprime (fst (quotient_of x)) (snd (quotient_of x))\<close>
        by (meson \<open>multiplicity (int p) (snd (quotient_of x)) \<noteq> 0\<close> coprime_common_divisor 
            multiplicity_unit_left)
      moreover have \<open>coprime (fst (quotient_of x)) (snd (quotient_of x))\<close>
        by (simp add: quotient_of_coprime)
      ultimately show ?thesis 
        by blast
    qed        
  qed
  moreover have \<open>prime p \<Longrightarrow> multiplicity p (1::nat) = 0\<close>
    for p::nat
    by simp    
  ultimately have \<open>snd (quotient_of x) = 1\<close>
    using multiplicity_eq_nat[where x = "nat (snd (quotient_of x))" and y = "(1::nat)" ]
    by (metis (full_types) less_irrefl_nat multiplicity_eq_int multiplicity_one not_prime_0
        prime_nat_iff_prime quotient_of_denom_pos' split_nat zero_less_one)    
  thus ?thesis
    by (metis Ints_of_int Rat.of_int_def eq_snd_iff quotient_of_inject quotient_of_int) 
qed

lemma integers_pval_D:
  \<open>x \<in> \<int> \<Longrightarrow> (\<And> p. prime p \<Longrightarrow> pval p x \<ge> 0)\<close>
proof-
  fix x::rat
  assume \<open>x \<in> \<int>\<close>
  show \<open>prime p \<Longrightarrow> pval p x \<ge> 0\<close> 
    for p
  proof-
    assume \<open>prime p\<close>
    have \<open>snd (quotient_of x) = 1\<close>
      using  \<open>x \<in> \<int>\<close>
      by (metis Ints_cases Rat.of_int_def quotient_of_int sndI)      
    hence \<open>multiplicity p  (snd (quotient_of x)) = 0\<close>
      by auto
    thus ?thesis
      unfolding pval_def
      by simp
  qed
qed

lemma integers_pval:
  \<open>x \<in> \<int> \<longleftrightarrow> (\<forall> p. prime p \<longrightarrow> pval p x \<ge> 0)\<close>
  using integers_pval_D integers_pval_I 
  by blast 

subsection \<open>p-adic norm\<close>

text\<open>
  We define the p-adic norm.
\<close>
definition pnorm :: \<open>nat \<Rightarrow> rat \<Rightarrow> real\<close> where
\<open>pnorm p x = (if x = 0 
  then 0
  else  p powr  (int (multiplicity p  (snd (quotient_of x)) )
               - int (multiplicity p  (fst (quotient_of x)) )) 
) \<close>

lemma pnorm_simplified:
\<open>x \<noteq> 0 \<Longrightarrow> pnorm p x = p powr  (- (pval p x) )\<close>
  unfolding pval_def pnorm_def
  by auto

lemma integers_pnorm_I:
  \<open>(\<And> p. prime p \<Longrightarrow> pnorm p x \<le> 1) \<Longrightarrow> x \<in> \<int>\<close>
proof(cases \<open>x = 0\<close>)
  case True
  thus ?thesis by auto
next
  case False
  assume \<open>\<And> p. prime p \<Longrightarrow> pnorm p x \<le> 1\<close>
  have \<open>prime p \<Longrightarrow> pval p x \<ge> 0\<close>
    for p
  proof-
    assume \<open>prime p\<close>
    hence \<open>pnorm p x \<le> 1\<close>
      using \<open>\<And> p. prime p \<Longrightarrow> pnorm p x \<le> 1\<close>
      by blast
    moreover have \<open>pnorm p x = p powr (- (pval p x))\<close>
      by (simp add: False pnorm_simplified)      
    ultimately have \<open> p powr (- (pval p x)) \<le> 1\<close>
      by simp
    moreover have \<open>p > 1\<close>
      using \<open>prime p\<close> prime_nat_iff 
      by blast      
    ultimately show \<open>pval p x \<ge> 0\<close>
      by (metis add.inverse_inverse neg_0_le_iff_le of_int_0_le_iff of_int_minus of_nat_1 
            of_nat_less_0_iff of_nat_less_iff powr_le_cancel_iff powr_zero_eq_one)      
  qed
  thus ?thesis
    using integers_pval_I by blast 
qed

lemma integers_pnorm_D:
  \<open>x \<in> \<int> \<Longrightarrow> (\<And> p. prime p \<Longrightarrow> pnorm p x \<le> 1)\<close>
proof(cases \<open>x = 0\<close>)
  case True
  thus \<open>prime p \<Longrightarrow> pnorm p x \<le> 1\<close> 
    for p 
  proof-
    assume \<open>prime p\<close>
    have \<open>pnorm p x = 0\<close>
      unfolding pnorm_def
      using True
      by auto
    thus ?thesis by auto
  qed
next
  case False
  assume \<open>x \<in> \<int>\<close>
  show \<open>prime p \<Longrightarrow> pnorm p x \<le> 1\<close> 
    for p
  proof-
    assume \<open>prime p\<close>
    hence \<open>pval p x \<ge> 0\<close>
      using  \<open>x \<in> \<int>\<close> integers_pval_D 
      by auto
    moreover have \<open>p > 1\<close>
      using \<open>prime p\<close> prime_nat_iff by blast
    moreover have \<open>pnorm p x = p powr (- (pval p x))\<close>
      using False
      by (simp add: pnorm_simplified) 
    ultimately show ?thesis
      by (metis less_one less_or_eq_imp_le negative_zle_0 of_int_le_0_iff of_nat_0_less_iff of_nat_1
          of_nat_le_iff powr_mono2' powr_one_eq_one zero_le_imp_eq_int)
  qed
qed

lemma integers_pnorm:
  \<open>x \<in> \<int> \<longleftrightarrow> (\<forall> p. prime p \<longrightarrow> pnorm p x \<le> 1)\<close>
  using integers_pnorm_D integers_pnorm_I 
  by blast

subsection \<open>Auxiliary results\<close>


subsection \<open>Main result\<close>

theorem harmonic_numbers_are_not_integers:
  fixes n :: nat
  assumes \<open>n \<ge> 2\<close>
  shows \<open>(\<Sum> k = 1..n. (Fract 1 (of_nat k)) ) \<notin> \<int>\<close>
proof-
  have \<open>pnorm 2 (\<Sum> k = 1..n. (Fract 1 (of_nat k)) ) > 1\<close>
    sorry
  thus ?thesis
    by (smt integers_pnorm_D two_is_prime_nat)     
qed

end

