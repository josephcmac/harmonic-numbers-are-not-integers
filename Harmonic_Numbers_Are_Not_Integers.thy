(*
  File:    Harmonic_Numbers_Are_Not_Integers.thy 
  Author:  Jose Manuel Rodriguez Caballero, University of Tartu
*)
section \<open>Harmonic numbers are not integers, except for the trivial case of 1\<close>
theory Harmonic_Numbers_Are_Not_Integers

imports 
  Complex_Main 
  Pnorm
begin

text \<open>
 In 1915, L. Theisinger ~\cite{theisinger1915bemerkung} proved that, except for the trivial 
 case of 1, the harmonic numbers are not integers. We formalize this result as theorem 
 @{text harmonic_numbers_are_not_integers}, which is deduced from the computation of the 
 2-adic norm of harmonic numbers (lemma @{text harmonic_numbers_2norm}).
\<close>


subsection \<open>Auxiliary result\<close>

lemma sum_last:
  fixes n::nat and a::\<open>nat \<Rightarrow> real\<close>
  assumes \<open>n \<ge> 2\<close>
  shows \<open>(\<Sum>k = 1..n - 1. (a k)) + (a n) =
    (\<Sum>k = 1..n. (a k))\<close>
  using \<open>n \<ge> 2\<close>
  apply auto
  by (smt Suc_leD le_add_diff_inverse numeral_1_eq_Suc_0 numeral_2_eq_2 numeral_One plus_1_eq_Suc sum.nat_ivl_Suc')

lemma harmonic_numbers_2norm:
  fixes n :: nat
  assumes \<open>n \<ge> 2\<close>
  shows \<open>pnorm 2 (\<Sum>k = 1..n. (Fract 1 (of_nat k))) = 2^(nat(\<lfloor>log 2 n\<rfloor>))\<close>
proof-
  define l where \<open>l = nat(\<lfloor>log 2 n\<rfloor>)\<close>
  define H where \<open>H = (\<Sum>k = 1..n. (Fract 1 (of_nat k)))\<close>
  have \<open>pnorm 2 ((2^l) * H) = 1\<close>
  proof-
    define pre_H where \<open>pre_H = (\<Sum>k = 1..(2^l-1). (Fract 1 (of_nat k)))\<close>
    define post_H where \<open>post_H = (\<Sum>k = (2^l+1)..n. (Fract 1 (of_nat k)))\<close>
    have \<open>H = pre_H + (Fract 1 (of_nat (2^l))) + post_H\<close>
    proof-
      have \<open>pre_H + (Fract 1 (of_nat (2^l))) = (\<Sum>k = 1..(2^l-1). (Fract 1 (of_nat k))) 
                  + (Fract 1 (of_nat (2^l)))\<close>
        unfolding pre_H_def
        by auto
      also have \<open>\<dots> = (\<Sum>k = 1..2^l. (Fract 1 (of_nat k)))\<close>
      proof-
        have \<open>l \<ge> 1\<close>
        proof-
          have \<open>log 2 n \<ge> 1\<close>
            using \<open>n \<ge> 2\<close>
            by auto
          hence \<open>\<lfloor>log 2 n\<rfloor> \<ge> 1\<close>
            by simp
          thus ?thesis 
            using \<open>l = nat(\<lfloor>log 2 n\<rfloor>)\<close> \<open>1 \<le> \<lfloor>log 2 (real n)\<rfloor>\<close> \<open>l = nat \<lfloor>log 2 (real n)\<rfloor>\<close> nat_mono 
            by presburger            
        qed
        hence \<open>(2::nat)^l \<ge> 2\<close>
        proof -
          have "(2::nat) ^ 1 \<le> 2 ^ l"
            by (metis \<open>1 \<le> l\<close> one_le_numeral power_increasing)
          then show ?thesis
            by (metis semiring_normalization_rules(33))
        qed
        hence \<open>(\<Sum>k = 1..2 ^ l - 1. real_of_rat (Fract 1 (int k))) 
                + real_of_rat (Fract 1 (int (2 ^ l))) 
                = (\<Sum>k = 1..2 ^ l. real_of_rat (Fract 1 (int k)))\<close>
          using sum_last[where n = \<open>2^l\<close> and a = \<open>(\<lambda> k. of_rat (Fract 1 (of_nat k)))\<close>]
          by auto
        moreover have \<open>(\<Sum>k = 1..2 ^ l - 1. real_of_rat (Fract 1 (int k))) 
                + real_of_rat (Fract 1 (int (2 ^ l)))
                = real_of_rat ((\<Sum>k = 1..2 ^ l - 1. (Fract 1 (int k))) 
                +  (Fract 1 (int (2 ^ l))))\<close>
          by (simp add: of_rat_add of_rat_sum)
        moreover have \<open>(\<Sum>k = 1..2 ^ l. real_of_rat (Fract 1 (int k)))
                      = real_of_rat (\<Sum>k = 1..2 ^ l. (Fract 1 (int k)))\<close>
          by (simp add: of_rat_sum)
        ultimately have \<open>real_of_rat ((\<Sum>k = 1..2 ^ l - 1. (Fract 1 (int k))) 
                +  (Fract 1 (int (2 ^ l)))) = real_of_rat (\<Sum>k = 1..2 ^ l. (Fract 1 (int k)))\<close>
          by simp
        thus ?thesis
          by simp
      qed
      finally have \<open>pre_H + Fract 1 (int (2 ^ l)) =
                  (\<Sum>k = 1..2 ^ l. Fract 1 (int k))\<close>
        by blast
      moreover have \<open>(\<Sum>k = 1..2 ^ l. Fract 1 (int k)) + post_H = H\<close>
      proof-
        have \<open>(\<Sum>k = 1..2 ^ l. Fract 1 (int k)) + post_H
              = (\<Sum>k = 1..2 ^ l. Fract 1 (int k)) +
                (\<Sum>k = 2 ^ l + 1..n. Fract 1 (int k))\<close>
          unfolding post_H_def
          by blast
        also have \<open>\<dots>  = (\<Sum>k = 1..n. Fract 1 (int k))\<close>
        proof-
          have \<open>2 ^ l \<le> n\<close>
          proof-
            have \<open>2 ^ l =  2 ^ nat \<lfloor>log 2 (real n)\<rfloor>\<close>
              unfolding l_def
              by simp
            also have \<open>\<dots> =  2 powr (nat \<lfloor>log 2 (real n)\<rfloor>)\<close>
              by (simp add: powr_realpow)              
            also have \<open>\<dots> \<le>  2 powr (log 2 (real n))\<close>
            proof-
              have \<open>\<lfloor>log 2 (real n)\<rfloor> \<le> log 2 (real n)\<close>
                by simp
              moreover have \<open>(2::real) > 1\<close>
                by simp
              ultimately show ?thesis 
                using Transcendental.powr_le_cancel_iff[where x = 2 
                    and a = "\<lfloor>log 2 (real n)\<rfloor>" and b = "log 2 (real n)"]
                using assms 
                by auto
            qed
            also have \<open>\<dots> = n\<close>
            proof-
              have \<open>(2::real) > 1\<close>
                by simp                
              moreover have \<open>n > 0\<close>
                using \<open>n \<ge> 2\<close>
                by auto
              ultimately show ?thesis
                by simp
            qed
            finally show ?thesis 
              by simp
          qed
          thus ?thesis
            by (metis le_add2 le_add_diff_inverse sum.ub_add_nat)
        qed
        finally have \<open>(\<Sum>k = 1..2 ^ l. Fract 1 (int k)) + post_H = (\<Sum>k = 1..n. Fract 1 (int k))\<close>
          by blast
        thus ?thesis
          unfolding pre_H_def H_def
          by blast
      qed
      ultimately show ?thesis
        by simp
    qed
    moreover have \<open>pnorm 2 ((2^l) * (Fract 1 (of_nat (2^l)))) = 1\<close>
    proof-
      have \<open>(2::nat)^l \<noteq> 0\<close>
        by auto
      hence \<open>((2::nat)^l) * (Fract 1 (of_nat ((2::nat)^l))) = 1\<close>
      proof -
        have "int (2 ^ l) \<noteq> 0"
          using \<open>2 ^ l \<noteq> 0\<close> by linarith
        hence "1 = Fract (int (2 ^ l) * 1) (int (2 ^ l) * 1)"
          by (metis (no_types) One_rat_def mult_rat_cancel)
        thus ?thesis
          by (metis (full_types) Fract_of_nat_eq mult_rat of_rat_1 of_rat_mult of_rat_of_nat_eq semiring_normalization_rules(7))
      qed        
      hence \<open>pnorm 2 (((2::rat)^l) * (Fract 1 (of_nat ((2::nat)^l)))) = pnorm 2 1\<close>
        by (metis (mono_tags, lifting) of_nat_numeral of_nat_power of_rat_1 of_rat_eq_iff 
            of_rat_mult of_rat_of_nat_eq)
      also have \<open>\<dots> = 1\<close>
        using pnorm_1
        by blast
      finally show ?thesis 
        by blast
    qed
    moreover have \<open>pnorm 2 ((2^l) * pre_H) < 1\<close>
      sorry
    ultimately have \<open>pnorm 2 ((2^l) * (Fract 1 (of_nat (2^l))) + (2^l) * pre_H) = 1\<close>
      using pnorm_unit_ball[where p = 2 and x = "(2^l) *  (Fract 1 (of_nat (2^l)))" and y = "(2^l) * pre_H"]
      by simp
    moreover have \<open>pnorm 2 ((2^l) * post_H) < 1\<close>
      sorry
    ultimately have \<open>pnorm 2 (((2^l) *  (Fract 1 (of_nat (2^l))) 
                                  + (2^l) * pre_H) + ((2^l) * post_H)) = 1\<close>
      using pnorm_unit_ball[where p = 2 and x = "(2^l) *  (Fract 1 (of_nat (2^l))) + (2^l) * pre_H" 
          and y = "(2^l) * post_H"]
      by simp
    thus ?thesis
      by (simp add: \<open>H = pre_H + Fract 1 (int (2 ^ l)) + post_H\<close> semiring_normalization_rules(24) semiring_normalization_rules(34))      
  qed
  hence \<open>(pnorm 2 (2^l)) * (pnorm 2 H) = 1\<close>
    using pnorm_multiplicativity
    by auto
  hence \<open>(1/2^l) * (pnorm 2 H) = 1\<close>
  proof-
    have \<open>prime (2::nat)\<close>
      by simp
    hence \<open>pnorm 2 (2^l) = 1/2^l\<close>
      using pnorm_primepow[where p = 2 and l = "l"] 
      by simp
    thus ?thesis
      using \<open>pnorm 2 (2 ^ l) * pnorm 2 H = 1\<close> 
      by auto
  qed
  hence \<open>pnorm 2 H = 2^l\<close>
    by simp    
  thus ?thesis
    using H_def l_def
    by blast
qed


subsection \<open>Main result\<close>

theorem harmonic_numbers_are_not_integers:
  fixes n :: nat
  assumes \<open>n \<ge> 2\<close>
  shows \<open>(\<Sum>k = 1..n. (Fract 1 (of_nat k)) ) \<notin> \<int>\<close>
proof-
  have \<open>pnorm 2 (\<Sum>k = 1..n. (Fract 1 (of_nat k)) ) > 1\<close>
    using harmonic_numbers_2norm[where n = "n"]  \<open>n \<ge> 2\<close>
    by auto    
  thus ?thesis
    by (smt integers_pnorm_D two_is_prime_nat)
qed

end

