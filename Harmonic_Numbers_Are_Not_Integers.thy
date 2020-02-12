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
 case of 1, the harmonic numbers are not integers. In 1918, 
 J. K{\"u}rsch{\'a}k  ~\cite{kurschak1918harmonic} provided a sufficient condition for the 
 difference between two harmonic numbers not to be an integer. We formalize these result as theorems
 @{text Taeisinger} and @{text Kurschak}, respectively. These results will be deduced from the 
 computation of the 2-adic norm of harmonic numbers (lemma @{text harmonic_numbers_2norm}).
\<close>

subsection \<open>Main definition\<close>


text \<open>
 We start by defining the harmonic numbers.
\<close>

fun harmonic :: \<open>nat \<Rightarrow> rat\<close> where
  \<open>harmonic 0 = 0\<close> |
  \<open>harmonic (Suc n) = harmonic n + Fract 1 (Suc n)\<close>

lemma harmonic_explicit:
  \<open>harmonic n = (\<Sum>k = 1..n. (Fract 1 (of_nat k)))\<close>
proof(induction n)
  case 0
  thus ?case
    by simp 
next
  case (Suc n)
  thus ?case
    by simp 
qed

lemma harmonic_diff_explicit:
  \<open>n \<ge> m+1 \<Longrightarrow> harmonic n - harmonic m = (\<Sum>k = m+1..n. (Fract 1 (of_nat k)))\<close>
proof-
  assume \<open>n \<ge> m+1\<close>
  then obtain k::nat where \<open>n = m + 1 + k\<close>
    using le_Suc_ex 
    by blast    
  show ?thesis
  proof -
    have "\<forall>n na f nb. \<not> (n::nat) \<le> na + 1 \<or> sum f {n..na + nb} = (sum f {n..na}::rat) + sum f {na + 1..na + nb}"
      by (meson sum.ub_add_nat)
    then show ?thesis
      by (metis (no_types) \<open>n = m + 1 + k\<close> add_diff_cancel_left' harmonic_explicit le_add2 linordered_field_class.sign_simps(1))
  qed 
qed

subsection \<open>Auxiliary result\<close>

lemma sum_last:
  fixes n::nat and a::\<open>nat \<Rightarrow> real\<close>
  assumes \<open>n \<ge> 2\<close>
  shows \<open>(\<Sum>k = 1..n - 1. (a k)) + (a n) = (\<Sum>k = 1..n. (a k))\<close>
  using \<open>n \<ge> 2\<close>
  apply auto
  by (smt Suc_leD le_add_diff_inverse numeral_1_eq_Suc_0 numeral_2_eq_2 numeral_One plus_1_eq_Suc sum.nat_ivl_Suc')

lemma harmonic_numbers_2norm:
  fixes n :: nat
  assumes \<open>n \<ge> 1\<close>
  shows \<open>pnorm 2 (harmonic n) = 2^(nat(\<lfloor>log 2 n\<rfloor>))\<close>
proof(cases \<open>n = 1\<close>)
  case True
  have \<open>prime (2::nat)\<close>
    by simp
  hence \<open>harmonic (1::nat) = 1\<close>
    by (simp add: One_rat_def)
  hence \<open>pnorm 2 (harmonic (1::nat)) = pnorm 2 1\<close>
    by simp
  also have \<open>\<dots> = 1\<close>
    by (simp add: pnorm_1)
  also have \<open>\<dots> = 2^(nat(\<lfloor>log 2 1\<rfloor>))\<close>
  proof-
    have \<open>log 2 1 = 0\<close>
      by simp
    hence \<open>\<lfloor>log 2 1\<rfloor> = 0\<close>
      by simp      
    thus ?thesis
      by auto
  qed
  finally show ?thesis
    using \<open>n = 1\<close>
    by auto
next
  case False
  hence \<open>n \<ge> 2\<close>
    using \<open>n \<ge> 1\<close>
    by auto
  define l where \<open>l = nat(\<lfloor>log 2 n\<rfloor>)\<close>
  define H where \<open>H = (\<Sum>k = 1..n. (Fract 1 (of_nat k)))\<close>
  have \<open>prime (2::nat)\<close>
    by simp
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
        have \<open>(\<Sum>k = 1..2 ^ l - 1. real_of_rat (Fract 1 (int k))) 
                + real_of_rat (Fract 1 (int (2 ^ l))) 
                = (\<Sum>k = 1..2 ^ l. real_of_rat (Fract 1 (int k)))\<close>
          using sum_last[where n = \<open>2^l\<close> and a = \<open>(\<lambda> k. of_rat (Fract 1 (of_nat k)))\<close>]
            \<open>(2::nat)^l \<ge> 2\<close>
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
    proof-
      have \<open>(2^l) * pre_H = (\<Sum>k = 1..2 ^ l - 1. (2^l) * (Fract 1 (int k)))\<close>
        unfolding pre_H_def
        using Groups_Big.semiring_0_class.sum_distrib_left[where r = \<open>2^l\<close> 
            and f = \<open>(\<lambda> k. Fract 1 (int k))\<close> and A = \<open>{1..(2^l - 1)}\<close>]
        by blast
      also have \<open>\<dots> = (\<Sum>k = 1..2 ^ l - 1. (Fract (2^l) (int k)))\<close>
        by (metis Fract_of_nat_eq mult.left_neutral mult.right_neutral mult_rat of_nat_numeral 
            of_nat_power)
      finally have \<open>2 ^ l * pre_H =
              (\<Sum>k = 1..2 ^ l - 1. Fract (2 ^ l) (int k))\<close>
        by blast
      hence \<open>pnorm 2 (2 ^ l * pre_H) =
              pnorm 2 (\<Sum>k = 1..2 ^ l - 1. Fract (2 ^ l) (int k))\<close>
        by simp
      also have \<open>\<dots> \<le>
              Max ((\<lambda> k. pnorm 2 (Fract (2 ^ l) (int k)))`{1..2^l-1})\<close>
      proof-
        have \<open>pnorm 2 (\<Sum>k = 1..2 ^ l - 1. Fract (2 ^ l) (int k))
           = pnorm 2 (sum (\<lambda> k. Fract (2 ^ l) (int k)) {1..(2::nat)^l-1})\<close>
          by blast
        also have \<open>\<dots> \<le> Max ((\<lambda> k. pnorm 2 (Fract (2 ^ l) (int k)))`{1..2^l-1})\<close>
          using \<open>prime 2\<close>  pnorm_ultratriangular_sum[where p = 2 and A = \<open>{1..2^l-1}\<close> 
              and x = \<open>(\<lambda> k. (Fract (2 ^ l) (int k)))\<close>]
          by (metis Nat.le_diff_conv2 \<open>2 \<le> 2 ^ l\<close> atLeastatMost_empty_iff2 finite_atLeastAtMost 
              nat_1_add_1 one_le_power prime_ge_1_nat)
        finally show ?thesis
          using \<open>pnorm 2 (\<Sum>k = 1..2 ^ l - 1. Fract (2 ^ l) (int k)) \<le> (MAX k\<in>{1..2 ^ l - 1}. 
              pnorm 2 (Fract (2 ^ l) (int k)))\<close> 
          by blast
      qed
      also have \<open>\<dots> < 1\<close>
      proof-
        have \<open>finite ((\<lambda> k. pnorm 2 (Fract (2 ^ l) (int k)))`{1..2^l-1})\<close>
          by blast          
        moreover have \<open>((\<lambda> k. pnorm 2 (Fract (2 ^ l) (int k)))`{1..2^l-1}) \<noteq> {}\<close>
        proof-
          have \<open>(1::nat) \<le> (2::nat)^l-1\<close>
            using \<open>(2::nat)^l \<ge> 2\<close>
            by auto
          hence \<open>{(1::nat)..(2::nat)^l-1} \<noteq> {}\<close>
            using Set_Interval.order_class.atLeastatMost_empty_iff2[where a = "1::nat" 
                and b = "(2::nat)^l - 1"]
            by auto
          thus ?thesis
            by blast
        qed
        moreover have \<open>x \<in> ((\<lambda> k. pnorm 2 (Fract (2 ^ l) (int k)))`{1..2^l-1}) \<Longrightarrow> x < 1\<close>
          for x
        proof-
          assume \<open>x \<in> ((\<lambda> k. pnorm 2 (Fract (2 ^ l) (int k)))`{1..2^l-1})\<close>
          then obtain k where \<open>x = pnorm 2 (Fract (2 ^ l) (int k))\<close> and \<open>k \<in> {1..2^l-1}\<close>
            by blast
          have \<open>pnorm 2 (Fract (2 ^ l) (int k)) < 1\<close>
          proof-
            have \<open>Fract (2 ^ l) (int k) = (2 ^ l)*(Fract 1 (int k))\<close>
              by (metis (no_types) Fract_of_nat_eq mult_numeral_1 mult_of_nat_commute mult_rat 
                  numeral_One of_nat_numeral of_nat_power)              
            hence \<open>pnorm 2 (Fract (2 ^ l) (int k)) = pnorm 2 ((2 ^ l)*(Fract 1 (int k)))\<close>
              by simp
            also have \<open>\<dots> < 1\<close>
            proof-
              have \<open>pnorm 2 ((2::rat)^l) = 1/(2::nat)^l\<close>
                using  \<open>prime (2::nat)\<close> pnorm_primepow[where p = "(2::nat)"]
                by auto
              moreover have \<open>pnorm 2 (Fract 1 k) < (2::nat)^l\<close>
              proof-
                have \<open>2 powr (- pval 2 (Fract 1 k)) < (2::nat)^l\<close>
                proof-
                  have \<open>pval 2 (Fract k 1) < l\<close>
                  proof-
                    have \<open>pval 2 (Fract k 1) = multiplicity (2::int) k\<close>
                      using \<open>prime 2\<close>  pval_integer[where p = 2 and k = k]
                      by auto
                    also have \<open>\<dots> < l\<close>
                    proof(rule classical)
                      assume \<open>\<not>(multiplicity 2 (int k) < int l)\<close>
                      hence \<open>multiplicity 2 (int k) \<ge> int l\<close>
                        by simp
                      hence \<open>((2::nat)^l) dvd k\<close>
                        by (metis (full_types) int_dvd_int_iff multiplicity_dvd' of_nat_numeral
                            of_nat_power zle_int)
                      hence \<open>(2::nat)^l \<le> k\<close>
                        using \<open>k \<in> {1..2 ^ l - 1}\<close> dvd_nat_bounds
                        by auto
                      moreover have \<open>k < (2::nat)^l\<close>
                        using  \<open>k\<in>{1..(2::nat)^l - 1}\<close>
                        by auto                        
                      ultimately show ?thesis
                        by linarith 
                    qed
                    finally show ?thesis
                      by blast
                  qed
                  hence \<open>- pval 2 (Fract 1 k) < l\<close>
                    using \<open>prime 2\<close> pval_inverse[where p = "2" and x = \<open>Fract 1 k\<close>] 
                      Fract_of_int_quotient 
                    by auto
                  hence \<open>2 powr (- pval 2 (Fract 1 k)) < 2 powr l\<close>
                    by auto
                  also have \<open>\<dots> = (2::nat)^l\<close>
                  proof -
                    have f1: "\<not> 2 \<le> (1::real)"
                      by auto
                    have f2: "\<forall>x1. ((1::real) < x1) = (\<not> x1 \<le> 1)"
                      by force
                    have "real (2 ^ l) = 2 ^ l"
                      by simp
                    hence "real l = log 2 (real (2 ^ l))"
                      using f2 f1 by (meson log_of_power_eq)
                    thus ?thesis
                      by simp
                  qed
                  finally show ?thesis 
                    by blast
                qed
                moreover have \<open>pnorm 2 (Fract 1 k) = 2 powr (- pval 2 (Fract 1 k))\<close>
                proof-
                  have \<open>k \<noteq> 0\<close>
                    using \<open>k\<in>{1..2^l - 1}\<close>
                    by simp
                  hence \<open>Fract 1 k \<noteq> 0\<close>
                    by (smt Fract_le_zero_iff le_numeral_extra(3) of_nat_le_0_iff)
                  thus \<open>pnorm 2 (Fract 1 k) = 2 powr (- pval 2 (Fract 1 k))\<close>
                    using \<open>prime 2\<close>
                    by (simp add: pnorm_simplified)
                qed
                ultimately show ?thesis
                  by simp
              qed
              moreover have \<open>pnorm 2 ((2::rat)^l) > 0\<close>
              proof-
                have \<open>(2::rat)^l \<noteq> 0\<close>
                  by simp                  
                moreover have \<open>pnorm 2 ((2::rat)^l) \<ge> 0\<close>
                  using \<open>prime (2::nat)\<close> pnorm_geq_zero
                  by simp                  
                ultimately show ?thesis
                  using pnorm_eq_zero \<open>prime (2::nat)\<close>
                  by (simp add: less_eq_real_def)                  
              qed
              moreover have \<open>pnorm 2 (Fract 1 k) > 0\<close>
              proof-
                have \<open>Fract 1 k \<noteq> 0\<close>
                  using \<open>k \<in> {1..2^l-1}\<close>
                  by (metis Fract_le_zero_iff atLeastAtMost_iff int.nat_pow_one int.zero_not_one int_ops(1) less_le_not_le less_one linorder_neqE_nat nat_int_comparison(2) not_less0 order_refl power2_less_eq_zero_iff)
                moreover have \<open>pnorm 2 (Fract 1 k) \<ge> 0\<close>
                  using \<open>prime (2::nat)\<close> pnorm_geq_zero
                  by blast
                ultimately show ?thesis
                  using pnorm_eq_zero \<open>prime (2::nat)\<close>
                  by (simp add: less_eq_real_def)                  
              qed
              ultimately have \<open>(pnorm 2 ((2::rat)^l))*(pnorm 2 (Fract 1 k)) 
                  < (1/(2::nat)^l)*((2::nat)^l)\<close>
                by simp
              also have \<open>\<dots> = 1\<close>
              proof-
                have \<open>(2::nat)^l \<noteq> 0\<close>
                  by simp                  
                thus ?thesis
                  by simp 
              qed
              finally have \<open>(pnorm 2 ((2::rat)^l))*(pnorm 2 (Fract 1 k)) < 1\<close>
                by blast
              moreover have \<open>(pnorm 2 ((2::rat)^l))*(pnorm 2 (Fract 1 k)) 
                  = pnorm 2 (2 ^ l * Fract 1 (int k))\<close>
                using \<open>prime 2\<close>
                by (simp add: pnorm_multiplicativity)
              ultimately show ?thesis
                by simp
            qed
            finally show \<open>pnorm 2 (Fract (2 ^ l) (int k)) < 1\<close>
              by blast
          qed
          thus ?thesis
            using \<open>x = pnorm 2 (Fract (2 ^ l) (int k))\<close>
            by blast
        qed
        ultimately show ?thesis 
          using Lattices_Big.linorder_class.Max_less_iff
            [where A = "((\<lambda> k. pnorm 2 (Fract (2 ^ l) (int k)))`{1..2^l-1})"]
          by blast
      qed
      finally show \<open>pnorm 2 (2 ^ l * pre_H) < 1\<close>
        by blast
    qed
    ultimately have \<open>pnorm 2 ((2^l) * (Fract 1 (of_nat (2^l))) + (2^l) * pre_H) = 1\<close>
      using pnorm_unit_ball[where p = 2 and x = "(2^l) *  (Fract 1 (of_nat (2^l)))" and y = "(2^l) * pre_H"]
      by simp
    moreover have \<open>pnorm 2 ((2^l) * post_H) < 1\<close>
    proof(cases \<open>2^l + 1 \<le> n\<close>)
      case True
      have \<open>pnorm 2 ((2^l) * post_H) = pnorm 2 (\<Sum>k = 2 ^ l + 1..n.  (2 ^ l)*(Fract 1 k))\<close>
      proof-
        have \<open>(2^l) * post_H = (\<Sum>k = 2 ^ l+1..n. (2 ^ l)*(Fract 1 k))\<close>
          unfolding post_H_def
          using Groups_Big.semiring_0_class.sum_distrib_left[where r = \<open>2^l\<close> 
              and f = \<open>(\<lambda> k. Fract 1 k)\<close> and A = \<open>{2 ^ l+1..n}\<close>]
          by auto
        thus ?thesis
          by simp
      qed
      also have \<open>\<dots>
           = pnorm 2 (sum (\<lambda> k. (2 ^ l)*(Fract 1 k)) {2 ^ l + 1..n})\<close>
        by blast
      also have \<open>\<dots>
           \<le> Max ((\<lambda> k. pnorm 2 ((2 ^ l)*(Fract 1 k))) ` {2 ^ l + 1..n})\<close>
      proof-
        have \<open>finite {2 ^ l + 1..n}\<close>
          by simp          
        moreover have \<open>{2 ^ l + 1..n} \<noteq> {}\<close>
          using True 
          by auto          
        ultimately show ?thesis 
          using \<open>prime 2\<close>  pnorm_ultratriangular_sum[where p = 2 and A = \<open>{2 ^ l + 1..n}\<close> 
              and x = \<open>(\<lambda> k. (2 ^ l)*(Fract 1 k))\<close>]
          by auto
      qed
      finally have \<open>pnorm 2 ((2^l) * post_H) \<le> 
          Max ((\<lambda> k. pnorm 2 ((2 ^ l)*(Fract 1 k))) ` {2 ^ l + 1..n})\<close>
        using \<open>pnorm 2 (2 ^ l * post_H) = pnorm 2 (\<Sum>k = 2 ^ l + 1..n. 2 ^ l * Fract 1 (int k))\<close> \<open>pnorm 2 (\<Sum>k = 2 ^ l + 1..n. 2 ^ l * Fract 1 (int k)) \<le> (MAX k\<in>{2 ^ l + 1..n}. pnorm 2 (2 ^ l * Fract 1 (int k)))\<close> 
        by linarith
      moreover have \<open>((\<lambda> k. pnorm 2 ((2 ^ l)*(Fract 1 k))) ` {2 ^ l + 1..n}) \<noteq> {}\<close>
        using True 
        by auto        
      moreover have \<open>finite ((\<lambda> k. pnorm 2 ((2 ^ l)*(Fract 1 k))) ` {2 ^ l + 1..n})\<close>
        by blast        
      moreover have \<open>x \<in> (\<lambda> k. pnorm 2 ((2 ^ l)*(Fract 1 k))) ` {2 ^ l + 1..n} \<Longrightarrow> x < 1\<close>
        for x
      proof-
        assume \<open>x \<in> (\<lambda> k. pnorm 2 ((2 ^ l)*(Fract 1 k))) ` {2 ^ l + 1..n}\<close>
        then obtain t where \<open>t \<in> {2 ^ l + 1..n}\<close> and \<open>x = pnorm 2 ((2 ^ l)*(Fract 1 t))\<close>
          by auto
        have  \<open>x = (pnorm 2 (2 ^ l)) * (pnorm 2 (Fract 1 t))\<close>
          using \<open>prime 2\<close> \<open>x = pnorm 2 ((2 ^ l)*(Fract 1 t))\<close> pnorm_multiplicativity
          by auto
        moreover have \<open>pnorm 2 (2 ^ l) = 1/(2^l)\<close>
          using \<open>prime 2\<close> pval_primepow[where p = "2::nat"]
          by (metis of_int_numeral of_nat_numeral pnorm_primepow)          
        moreover have \<open>pnorm 2 (Fract 1 t) < 2^l\<close>
        proof(rule classical)
          assume \<open>\<not> (pnorm 2 (Fract 1 t) < 2^l)\<close>
          hence \<open>pnorm 2 (Fract 1 t) \<ge> 2^l\<close>
            by auto
          moreover have \<open>2 powr l = 2^l\<close>
            using powr_realpow 
            by auto            
          ultimately have \<open>pnorm 2 (Fract 1 t) \<ge> 2 powr l\<close>
            by auto
          moreover have \<open>pnorm 2 (Fract 1 t) = 2 powr (-pval 2 (Fract 1 t))\<close>
          proof-
            have \<open>t \<noteq> 0\<close>
              using \<open>t \<in> {2^l + 1 .. n}\<close>
              by simp
            hence \<open>Fract 1 t \<noteq> 0\<close>
            proof -
              have "\<not> int t \<le> 0"
                by (metis \<open>t \<noteq> 0\<close> of_nat_le_0_iff)
              hence "\<not> Fract 1 (int t) \<le> 0"
                by (simp add: Fract_le_zero_iff)
              thus ?thesis
                by linarith
            qed              
            thus ?thesis 
              using pnorm_simplified
              by simp
          qed
          ultimately have \<open>-pval 2 (Fract 1 t) \<ge> l\<close>
            by simp            
          hence \<open>-(multiplicity 2 (fst (quotient_of (Fract 1 t))))
               + (multiplicity 2 (snd (quotient_of (Fract 1 t))))
                     \<ge> l\<close>
            unfolding pval_def 
            by auto
          have \<open>quotient_of (Fract (1::int) t) = (1, t)\<close>
          proof-
            have \<open>coprime (1::int) t\<close>
              by simp              
            moreover have \<open>t > 0\<close>
              using \<open>t \<in> {2^l + 1 .. n}\<close>
              by simp
            ultimately show ?thesis
              by (simp add: quotient_of_Fract)              
          qed
          hence \<open>fst (quotient_of (Fract 1 t)) = 1\<close>
            by simp
          moreover have \<open>snd (quotient_of (Fract 1 t)) = t\<close>
            using \<open>quotient_of (Fract (1::int) t) = (1, t)\<close>
            by auto
          ultimately have \<open>- int(multiplicity (2::int) 1) + int(multiplicity (2::int) t) \<ge> l\<close>
            using \<open>-(multiplicity 2 (fst (quotient_of (Fract 1 t))))
               + (multiplicity 2 (snd (quotient_of (Fract 1 t))))
                     \<ge> l\<close>
            by auto
          moreover have \<open>multiplicity (2::int) 1 = 0\<close>
            by simp
          ultimately have \<open>multiplicity (2::int) t \<ge> l\<close>
            by auto
          hence \<open>2^l dvd t\<close>
            by (metis int_dvd_int_iff multiplicity_dvd' of_nat_numeral of_nat_power)
          hence \<open>\<exists> k::nat. 2^l * k = t\<close>
            by auto
          then obtain k::nat where \<open>2^l * k = t\<close>
            by blast
          have \<open>k \<ge> 2\<close>
          proof(rule classical)
            assume \<open>\<not>(k \<ge> 2)\<close>
            hence \<open>k < 2\<close>
              by simp
            moreover have \<open>k \<noteq> 0\<close>
            proof(rule classical)
              assume \<open>\<not>(k \<noteq> 0)\<close>
              hence \<open>k = 0\<close>
                by simp
              hence \<open>t = 0\<close>
                using \<open>2^l * k = t\<close>
                by auto
              thus ?thesis
                using \<open>t \<in> {2^l + 1 .. n}\<close>
                by auto
            qed
            moreover have \<open>k \<noteq> 1\<close>
            proof(rule classical)
              assume \<open>\<not>(k \<noteq> 1)\<close>
              hence \<open>k = 1\<close>
                by simp
              hence \<open>t = 2^l\<close>
                using \<open>2^l * k = t\<close>
                by auto
              thus ?thesis
                using \<open>t \<in> {2^l + 1 .. n}\<close>
                by auto
            qed
            ultimately show ?thesis
              by auto
          qed
          hence \<open>2^(Suc l) \<le> t\<close>
            using \<open>2 ^ l * k = t\<close> 
            by auto
          hence \<open>2^(Suc l) \<le> n\<close>
            using \<open>t \<in> {2^l + 1 .. n}\<close>
            by auto
          moreover have \<open>n < 2^(Suc l)\<close>
          proof -
            have f1: "\<forall>n na. (n \<le> na) = (int n + - 1 * int na \<le> 0)"
              by auto
            have f2: "int (Suc (nat \<lfloor>log 2 (real n)\<rfloor>)) + - 1 * int (Suc l) \<le> 0"
              by (simp add: l_def)
            have f3: "(- 1 * log 2 (real n) + real (Suc l) \<le> 0) = (0 \<le> log 2 (real n) + - 1 * real (Suc l))"
              by fastforce
            have f4: "real (Suc l) + - 1 * log 2 (real n) = - 1 * log 2 (real n) + real (Suc l)"
              by auto
            have f5: "\<forall>n na. \<not> 2 ^ n \<le> na \<or> real n + - 1 * log 2 (real na) \<le> 0"
              by (simp add: le_log2_of_power)
            have f6: "\<forall>x0 x1. (- 1 * int x0 + int (2 ^ x1) \<le> 0) = (0 \<le> int x0 + - 1 * int (2 ^ x1))"
              by auto
            have f7: "\<forall>x0 x1. int (2 ^ x1) + - 1 * int x0 = - 1 * int x0 + int (2 ^ x1)"
              by auto
            have "\<not> 0 \<le> log 2 (real n) + - 1 * real (Suc l)"
              using f2 by linarith
            then have "\<not> 0 \<le> int n + - 1 * int (2 ^ Suc l)"
              using f7 f6 f5 f4 f3 f1 by (metis (no_types))
            then show ?thesis
              by linarith
          qed                    
          ultimately show ?thesis
            by auto
        qed
        moreover have \<open>pnorm 2 (2 ^ l) \<ge> 0\<close>
          using \<open>prime 2\<close> pnorm_geq_zero 
          by blast
        moreover have \<open>pnorm 2 (Fract 1 t) \<ge> 0\<close>
          using \<open>prime 2\<close> pnorm_geq_zero 
          by blast
        ultimately show ?thesis 
          by simp
      qed
      ultimately show ?thesis
        by (smt Max_in)
    next
      case False
      hence \<open>2 ^ l + 1 > n\<close>
        by simp
      hence \<open>{2 ^ l + 1..n} = {}\<close>
        by simp
      hence \<open>post_H = 0\<close>
        unfolding post_H_def
        by simp        
      hence \<open>(2^l) * post_H = 0\<close>
        by (simp add: \<open>post_H = 0\<close>)        
      thus ?thesis
        unfolding pnorm_def
        by auto
    qed
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
    using H_def l_def harmonic_explicit[where n = n]
    by simp   
qed


subsection \<open>Main results\<close>

text\<open>The following result is due to L. Taeisinger ~\cite{theisinger1915bemerkung}.\<close>
theorem Taeisinger:
  fixes n :: nat
  assumes \<open>n \<ge> 2\<close>
  shows \<open>harmonic n \<notin> \<int>\<close>
proof-
  have \<open>pnorm 2 (\<Sum>k = 1..n. (Fract 1 (of_nat k)) ) > 1\<close>
    using harmonic_numbers_2norm[where n = "n"] \<open>n \<ge> 2\<close> harmonic_explicit 
    by auto    
  thus ?thesis
  proof -
    have "\<not> pnorm 2 (\<Sum>n = 1..n. Fract 1 (int n)) \<le> 1"
      using \<open>1 < pnorm 2 (\<Sum>k = 1..n. Fract 1 (int k))\<close> by linarith
    then show ?thesis
      by (metis (no_types) harmonic_explicit integers_pnorm_D two_is_prime_nat)
  qed
qed

text\<open>The following result is due to J. K{\"u}rsch{\'a}k  ~\cite{kurschak1918harmonic}.\<close>
theorem Kurschak:
  fixes n m :: nat
  assumes \<open>m + 2 \<le> n\<close>
  shows \<open>harmonic n - harmonic m \<notin> \<int>\<close>
proof(cases \<open>2*m \<le> n\<close>)
  case True
  show ?thesis
  proof(cases \<open>m = 0\<close>)
    case True
    thus ?thesis
      using Taeisinger assms 
      by auto 
  next
    case False
    hence \<open>m \<ge> 1\<close>
      by simp
    have \<open>n \<ge> 2\<close>
      using \<open>m+2 \<le> n\<close>
      by auto
    have \<open>prime (2::nat)\<close>
      by auto
    have \<open>harmonic n = (harmonic n - harmonic m) + (harmonic m)\<close>
      by simp
    hence \<open>pnorm 2 (harmonic n) \<le> max (pnorm 2 (harmonic n - harmonic m)) (pnorm 2 (harmonic m))\<close>
      using \<open>prime 2\<close> pnorm_ultratriangular[where p = "2::nat" and x = "harmonic n - harmonic m" 
          and y = "harmonic m"]
      by auto
    moreover have \<open>pnorm 2 (harmonic m) < pnorm 2 (harmonic n)\<close>
    proof-
      have \<open>pnorm 2 (harmonic m) =  2 ^ nat \<lfloor>log 2 (real m)\<rfloor>\<close>
        using harmonic_numbers_2norm[where n = "n"] \<open>m \<ge> 1\<close>
        by (meson \<open>1 \<le> m\<close> harmonic_numbers_2norm)
      moreover have \<open>pnorm 2 (harmonic n) =  2 ^ nat \<lfloor>log 2 (real n)\<rfloor>\<close>
        using harmonic_numbers_2norm[where n = "n"] \<open>2 \<le> n\<close> 
        by linarith
      moreover have \<open>(2::nat) ^ nat \<lfloor>log 2 (real m)\<rfloor> < (2::nat) ^ nat \<lfloor>log 2 (real n)\<rfloor>\<close>
      proof-
        have \<open>log 2 (real m) + 1 = log 2 (real m) + log 2 (2::real)\<close>
        proof-
          have \<open>log 2 (real 2) = 1\<close>
            by simp
          thus ?thesis 
            by simp
        qed
        also have \<open>\<dots> = log 2 ((real m) * (2::real)) \<close>
        proof-
          have \<open>(2::real) > 0\<close>
            by simp
          moreover have \<open>(2::real) \<noteq> 1\<close>
            by simp
          moreover have \<open>m > 0\<close>
            using False 
            by auto            
          ultimately show ?thesis
            using log_mult[where a = 2 and x = "real m" and y = "2::real"]
            by simp
        qed
        also have \<open>\<dots> = log 2 (2*real m) \<close>
        proof-
          have \<open>(real m)*(2::real) = 2*m\<close>
            by auto
          thus ?thesis
            by (simp add: \<open>real m * 2 = real (2 * m)\<close>)             
        qed
        also have \<open>\<dots> \<le> log 2 (real n)\<close>
          using \<open>2*m \<le> n\<close>  \<open>m \<noteq> 0\<close>
          by auto
        finally have \<open>log 2 (real m) + 1 \<le> log 2 (real n)\<close>
          by blast
        hence \<open>\<lfloor>log 2 (real m)\<rfloor> < \<lfloor>log 2 (real n)\<rfloor>\<close>
          by linarith          
        moreover have \<open>(2::nat) > 1\<close>
          by auto
        ultimately show ?thesis
          by (smt \<open>1 \<le> m\<close> floor_less_zero log_less_zero_cancel_iff nat_mono_iff of_nat_1 
              of_nat_mono power_strict_increasing)
      qed
      ultimately show ?thesis 
        by auto
    qed
    ultimately have \<open>pnorm 2 (harmonic n) \<le> pnorm 2 (harmonic n - harmonic m)\<close>
      by linarith
    moreover have \<open>1 < pnorm 2 (harmonic n)\<close>
      using harmonic_numbers_2norm[where n = "n"] \<open>n \<ge> 2\<close>
      by auto
    ultimately have \<open>1 < pnorm 2 (harmonic n - harmonic m) \<close>
      by auto
    thus ?thesis
      using integers_pnorm_D[where p = "2::nat" and x = "harmonic n - harmonic m"] \<open>prime 2\<close>
      by auto      
  qed
next
  case False
  have explicit: \<open>harmonic n - harmonic m = (\<Sum>k = m + 1..n. Fract 1 (int k))\<close>
    using \<open>n \<ge> m + 2\<close> harmonic_diff_explicit[where m = m and n = n]
    by linarith
  have \<open>harmonic n - harmonic m < 1\<close>
  proof-
    have \<open>(\<Sum>k = m + 1..n. Fract 1 (int k)) < 1\<close>
    proof-
      have \<open>finite {m + 1..n}\<close>
        by simp
      moreover have \<open>{m + 1..n} \<noteq> {}\<close>
        using \<open>m+2 \<le> n\<close>
        by simp
      moreover have \<open>k \<in> {m + 1..n} \<Longrightarrow> Fract 1 k \<le> Fract 1 (m+1)\<close>
        for k
      proof-
        assume \<open>k \<in> {m + 1..n}\<close>
        have \<open>k \<ge> m+1\<close>
          using \<open>k \<in> {m + 1..n}\<close>
          by auto
        thus ?thesis
          by auto
      qed
      ultimately have \<open>(\<Sum>k = m + 1..n. Fract 1 k) \<le> of_nat (card {m + 1..n})*Fract 1 (int (m + 1))\<close>
        using  Groups_Big.sum_bounded_above[where A = "{m+1..n}" and K = "Fract 1 (m+1)"
            and f = "\<lambda> k. Fract 1 k"]
        by auto
      also  have \<open>\<dots> \<le> of_nat m*Fract 1 ((m + 1))\<close>
      proof-
        have \<open>card {m+1..n} \<le> m\<close>
        proof-
          have \<open>card {m+1..n} = n - m\<close>
            by auto
          thus ?thesis
            using False
            by simp
        qed
        moreover have \<open>card  {m + 1..n} > 0\<close>
          using \<open>{m + 1..n} \<noteq> {}\<close> card_gt_0_iff 
          by blast          
        ultimately show ?thesis
          by (smt add_is_0 less_eq_rat_def mult_mono of_nat_0_le_iff of_nat_le_0_iff of_nat_mono 
              zero_le_Fract_iff)
      qed
      also have \<open>\<dots> < 1\<close>
      proof -
        have "Fract (int m * 1) (int (1 + m)) < 1"
          by (simp add: Fract_less_one_iff)
        then show ?thesis
          by (metis (no_types) Fract_of_nat_eq add.commute mult.left_neutral mult_rat)
      qed
      finally show ?thesis
        by blast
    qed
    thus ?thesis
      using explicit 
      by simp
  qed
  moreover have \<open>0 < harmonic n - harmonic m\<close>
  proof-
    have \<open>finite {m + 1..n}\<close>
      by simp
    moreover have \<open>{m + 1..n} \<noteq> {}\<close>
      using \<open>m+2 \<le> n\<close>
      by simp
    moreover have \<open>k \<in> {m + 1..n} \<Longrightarrow> 0 < Fract 1 k\<close>
      for k
    proof-
      assume \<open>k \<in> {m + 1..n}\<close>
      hence \<open>k \<ge> 1\<close>
        by auto
      thus ?thesis
        by (simp add: zero_less_Fract_iff) 
    qed
    ultimately have \<open>0 < (\<Sum>k = m + 1..n. Fract 1 k)\<close>
      using Groups_Big.ordered_comm_monoid_add_class.sum_pos[where I = "{m+1..n}" 
          and f = "\<lambda> k. Fract 1 k"]
      by blast
    thus ?thesis
      using explicit 
      by simp
  qed
  ultimately show ?thesis
  proof -
    have f1: "sgn (harmonic n - harmonic m) = 1"
      by (metis \<open>0 < harmonic n - harmonic m\<close> sgn_pos)
    have "0 \<le> harmonic n - harmonic m"
      by (metis \<open>0 < harmonic n - harmonic m\<close> less_eq_rat_def)
    thus ?thesis
      using f1 by (metis (no_types) Ints_0 \<open>harmonic n - harmonic m < 1\<close> eq_iff_diff_eq_0 frac_eq_0_iff frac_unique_iff sgn_if zero_neq_one)
  qed    
qed

end

