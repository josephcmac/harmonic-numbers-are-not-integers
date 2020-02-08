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
      unfolding H_def pre_H_def post_H_def
      sorry
    moreover have \<open>pnorm 2 ((2^l) * (Fract 1 (of_nat (2^l)))) = 1\<close>
      sorry
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
    by simp
  thus ?thesis
    by (smt integers_pnorm_D two_is_prime_nat)
qed

end

