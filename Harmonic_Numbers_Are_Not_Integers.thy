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

lemma pval_unit_dvd_I:
  \<open>prime p \<Longrightarrow> x \<noteq> 0  \<Longrightarrow> pval p x = 0 \<Longrightarrow> 
       \<not>(p dvd (fst (quotient_of x)))
     \<and> \<not>(p dvd (snd (quotient_of x)))\<close>
proof-
  assume \<open>prime p\<close> and \<open>x \<noteq> 0\<close> and \<open>pval p x = 0\<close>
  have \<open>pval p x = (multiplicity p (fst (quotient_of x))) - (multiplicity p (snd (quotient_of x)))\<close>
    using \<open>pval p x = 0\<close> pval_def 
    by auto
  hence \<open>(multiplicity p (fst (quotient_of x))) = (multiplicity p (snd (quotient_of x)))\<close>
    using \<open>pval p x = 0\<close>
    by (simp add: pval_def)
  show ?thesis
  proof(rule classical)
    assume \<open>\<not> (\<not>(p dvd (fst (quotient_of x))) \<and> \<not>(p dvd (snd (quotient_of x))))\<close>
    hence \<open>(p dvd (fst (quotient_of x))) \<or> (p dvd (snd (quotient_of x)))\<close>
      by blast
    have \<open>(p dvd (fst (quotient_of x))) \<and> (p dvd (snd (quotient_of x)))\<close>      
    proof(cases \<open>p dvd (fst (quotient_of x))\<close>)
      case True
      moreover have \<open>\<not> is_unit (int p)\<close>
        using \<open>prime p\<close> 
        by auto
      moreover have \<open>fst (quotient_of x) \<noteq> 0\<close>
      proof(rule classical)
        assume \<open>\<not> ( fst (quotient_of x) \<noteq> 0 )\<close>
        hence \<open>fst (quotient_of x) = 0\<close>
          by blast
        show ?thesis
          by (metis Fract_of_int_quotient Zero_rat_def \<open>x \<noteq> 0\<close>  eq_rat(3) prod.collapse 
              quotient_of_div)          
      qed
      ultimately have \<open>multiplicity p (fst (quotient_of x)) \<ge> 1\<close>
        using multiplicity_geI[where n = 1 and p = p and x = "fst (quotient_of x)"]
        by simp
      hence \<open>multiplicity p (snd (quotient_of x)) \<ge> 1\<close>
        using \<open>multiplicity (int p) (fst (quotient_of x)) = multiplicity (int p) (snd (quotient_of x))\<close> 
        by linarith
      hence \<open>p dvd (snd (quotient_of x))\<close>
        using le_numeral_extra(2) not_dvd_imp_multiplicity_0 ord_le_eq_trans 
        by blast
      thus ?thesis
        by (simp add: True) 
    next
      case False
      hence \<open>p dvd (snd (quotient_of x))\<close>
        using \<open>int p dvd fst (quotient_of x) \<or> int p dvd snd (quotient_of x)\<close> 
        by auto
      moreover have \<open>\<not> is_unit (int p)\<close>
        using \<open>prime p\<close> 
        by auto
      moreover have \<open>snd (quotient_of x) \<noteq> 0\<close>
        by (metis less_int_code(1) quotient_of_denom_pos')      
      ultimately have \<open>multiplicity p (snd (quotient_of x)) \<ge> 1\<close>
        using multiplicity_geI[where n = 1 and p = p and x = "snd (quotient_of x)"]
        by simp
      hence \<open>multiplicity p (fst (quotient_of x)) \<ge> 1\<close>
        using \<open>multiplicity (int p) (fst (quotient_of x)) = multiplicity (int p) (snd (quotient_of x))\<close> 
        by linarith
      hence \<open>p dvd (fst (quotient_of x))\<close>
        using le_numeral_extra(2) not_dvd_imp_multiplicity_0 ord_le_eq_trans 
        by blast
      thus ?thesis
        by (simp add: False) 
    qed
    moreover have \<open>coprime (fst (quotient_of x)) (snd (quotient_of x))\<close>
      using Rat.quotient_of_coprime
      by simp
    ultimately show ?thesis
      by (meson \<open>prime p\<close> not_coprimeI not_prime_unit prime_nat_int_transfer)       
  qed
qed

lemma pval_unit_dvd_D:
  \<open>prime p \<Longrightarrow> x \<noteq> 0 
     \<Longrightarrow> \<not>(p dvd (fst (quotient_of x)))
     \<Longrightarrow> \<not>(p dvd (snd (quotient_of x)))
     \<Longrightarrow> pval p x = 0\<close>
proof-
  assume \<open>prime p\<close> and \<open>x \<noteq> 0\<close> and \<open>\<not>(p dvd (fst (quotient_of x)))\<close> 
    and \<open>\<not>(p dvd (snd (quotient_of x)))\<close>
  have \<open>multiplicity p (fst (quotient_of x)) = 0\<close>
    using  \<open>\<not>(p dvd (fst (quotient_of x)))\<close>
    by (simp add: not_dvd_imp_multiplicity_0)
  moreover have \<open>multiplicity p (snd (quotient_of x)) = 0\<close>
    using  \<open>\<not>(p dvd (snd (quotient_of x)))\<close>
    by (simp add: not_dvd_imp_multiplicity_0)
  ultimately show ?thesis
    by (simp add: pval_def) 
qed

lemma pval_unit_dvd:
  \<open>prime p \<Longrightarrow> x \<noteq> 0 \<Longrightarrow> (
       \<not>(p dvd (fst (quotient_of x)))
     \<and> \<not>(p dvd (snd (quotient_of x)))) \<longleftrightarrow> pval p x = 0\<close>
  using pval_unit_dvd_D pval_unit_dvd_I 
  by blast

lemma pval_composition_of_units:
  \<open>prime p \<Longrightarrow> u \<noteq> 0 \<Longrightarrow> v \<noteq> 0 \<Longrightarrow> pval p u = 0 \<Longrightarrow> pval p v = 0 \<Longrightarrow> pval p (u * v) = 0\<close>
proof-
  assume \<open>prime p\<close> and \<open>u \<noteq> 0\<close> and \<open>v \<noteq> 0\<close> and \<open>pval p u = 0\<close> and \<open>pval p v = 0\<close>
  have \<open>\<not>(p dvd (fst (quotient_of u)))\<close>
    using \<open>pval p u = 0\<close> pval_unit_dvd_I \<open>prime p\<close> \<open>u \<noteq> 0\<close> 
    by blast
  moreover have \<open>\<not>(p dvd (fst (quotient_of v)))\<close>
    using \<open>pval p v = 0\<close> pval_unit_dvd_I \<open>prime p\<close> \<open>v \<noteq> 0\<close> 
    by blast
  ultimately have \<open>\<not>(p dvd ((fst (quotient_of u))*(fst (quotient_of v))))\<close>
    by (meson \<open>prime p\<close> prime_dvd_multD prime_nat_int_transfer)
  have \<open>\<not>(p dvd (snd (quotient_of u)))\<close>
    using \<open>pval p u = 0\<close> pval_unit_dvd_I \<open>prime p\<close> \<open>u \<noteq> 0\<close> 
    by blast
  moreover have \<open>\<not>(p dvd (snd (quotient_of v)))\<close>
    using \<open>pval p v = 0\<close> pval_unit_dvd_I \<open>prime p\<close> \<open>v \<noteq> 0\<close> 
    by blast
  ultimately have \<open>\<not>(p dvd ((snd (quotient_of u))*(snd (quotient_of v))))\<close>
    by (meson \<open>prime p\<close> prime_dvd_multD prime_nat_int_transfer)
  have \<open>u * v =  ((fst (quotient_of u))*(fst (quotient_of v))) /
                 ((snd (quotient_of u))*(snd (quotient_of v)))\<close>
  proof-
    have \<open>u = (fst (quotient_of u)) / (snd (quotient_of u))\<close>
    proof -
      have f1: "u = rat_of_int (fst (quotient_of u)) / rat_of_int (snd (quotient_of u))"
        by (meson prod.exhaust_sel quotient_of_div)
      have "rat_of_int (snd (quotient_of u)) \<noteq> 0"
        by (metis (no_types) \<open>\<not> int p dvd snd (quotient_of u)\<close> dvd_0_right of_int_eq_0_iff)
      then show ?thesis
        using f1 by (metis (full_types) nonzero_of_rat_divide of_rat_of_int_eq of_real_divide of_real_of_int_eq)
    qed
    moreover have \<open>v = (fst (quotient_of v)) / (snd (quotient_of v))\<close>
    proof -
      have f1: "v = rat_of_int (fst (quotient_of v)) / rat_of_int (snd (quotient_of v))"
        by (meson prod.exhaust_sel quotient_of_div)
      have "rat_of_int (snd (quotient_of v)) \<noteq> 0"
        by (metis \<open>\<not> int p dvd snd (quotient_of v)\<close> dvd_0_right of_int_eq_0_iff)
      then show ?thesis
        using f1 by (metis (full_types) nonzero_of_rat_divide of_rat_of_int_eq of_real_divide of_real_of_int_eq)
    qed      
    ultimately show ?thesis
      by (simp add: of_rat_mult) 
  qed
  hence \<open>u * v =  Fract ((fst (quotient_of u))*(fst (quotient_of v))) 
                 ((snd (quotient_of u))*(snd (quotient_of v)))\<close>
    by (metis (no_types, lifting) \<open>u \<noteq> 0\<close> \<open>v \<noteq> 0\<close> divide_eq_0_iff divisors_zero of_int_0_eq_iff of_rat_0 of_rat_eq_iff of_rat_rat of_real_divide of_real_of_int_eq)
  define d where \<open>d = gcd ((fst (quotient_of u))*(fst (quotient_of v))) ((snd (quotient_of u))*(snd (quotient_of v)))\<close>
  define z::\<open>int*int\<close> where \<open>z = ( ((fst (quotient_of u))*(fst (quotient_of v))) div d, 
                                  ((snd (quotient_of u))*(snd (quotient_of v))) div d )\<close>

  have \<open>u * v =  Fract (fst z) (snd z)\<close>
    unfolding z_def
    by (simp add: Fract_coprime \<open>u * v = Fract (fst (quotient_of u) * fst (quotient_of v)) (snd (quotient_of u) * snd (quotient_of v))\<close> d_def)
  moreover have \<open>snd z > 0\<close>
  proof-
    have \<open>snd (quotient_of u) > 0\<close>
      by (simp add: quotient_of_denom_pos')
    moreover have \<open>snd (quotient_of v) > 0\<close>
      by (simp add: quotient_of_denom_pos')      
    moreover have \<open>d \<noteq> 0\<close>
      unfolding d_def
      using \<open>\<not> int p dvd fst (quotient_of u) * fst (quotient_of v)\<close> by auto
    ultimately show ?thesis 
      unfolding z_def
      by (smt \<open>u * v = Fract (fst z) (snd z)\<close> \<open>u \<noteq> 0\<close> \<open>v \<noteq> 0\<close> d_def gcd_pos_int mult_pos_pos no_zero_divisors pos_imp_zdiv_neg_iff rat_number_collapse(6) snd_conv z_def)
  qed
  moreover have \<open>coprime (fst z) (snd z)\<close>
    unfolding z_def
    using \<open>\<not> int p dvd fst (quotient_of u) * fst (quotient_of v)\<close> d_def div_gcd_coprime dvd_0_right
    by (metis fst_conv snd_conv)
  ultimately have \<open>u * v = Fract (fst z) (snd z) \<and>
        (0::int) < snd z \<and> coprime (fst z) (snd z)\<close>
    by auto
  hence \<open>quotient_of (u * v) = z\<close>
    unfolding quotient_of_def
    using quotient_of_unique by blast
  hence \<open>fst (quotient_of (u * v)) dvd ((fst (quotient_of u))*(fst (quotient_of v)))\<close>
    unfolding z_def
    by (metis d_def dvd_mult_div_cancel dvd_triv_right fst_conv gcd_dvd1)
  hence \<open>\<not>(p dvd fst (quotient_of (u * v)))\<close>
    using \<open>\<not> int p dvd fst (quotient_of u) * fst (quotient_of v)\<close> dvd_trans 
    by blast
  from \<open>quotient_of (u * v) = z\<close>
  have \<open>snd (quotient_of (u * v)) dvd ((snd (quotient_of u))*(snd (quotient_of v)))\<close>
    unfolding z_def
    by (metis d_def dvd_def dvd_div_mult_self gcd_dvd2 snd_conv)    
  hence \<open>\<not>(p dvd snd (quotient_of (u * v)))\<close>
    using \<open>\<not> int p dvd snd (quotient_of u) * snd (quotient_of v)\<close> dvd_trans 
    by blast    
  thus ?thesis 
    using \<open>\<not>(p dvd fst (quotient_of (u * v)))\<close>
    by (simp add: \<open>prime p\<close> \<open>u \<noteq> 0\<close> \<open>v \<noteq> 0\<close> pval_unit_dvd_D)
qed

lemma multiplicity_quotient_fst: 
  \<open>(multiplicity (int p) (fst (quotient_of (1 / x)))) 
        = (multiplicity (int p) (snd (quotient_of x)))\<close>
proof(cases \<open>x = 0\<close>)
  case True
  thus ?thesis
    by (simp add: True) 
next
  case False
  hence \<open>x \<noteq> 0\<close>
    by blast
  show ?thesis 
  proof(cases \<open>x > 0\<close>)
    case True
    hence \<open>\<exists> u v. x = Fract u v \<and> gcd u v = 1 \<and> u > 0 \<and> v > 0\<close>
      by (metis \<open>x \<noteq> 0\<close> Rat_cases_nonzero coprime_imp_gcd_eq_1 zero_less_Fract_iff)
    then obtain u v where \<open>x = Fract u v\<close> and \<open>gcd u v = 1\<close> and \<open>u > 0\<close> and \<open>v > 0\<close>
      by auto
    have \<open>quotient_of x = (u, v)\<close>
      using \<open>0 < v\<close> \<open>gcd u v = 1\<close> \<open>x = Fract u v\<close> int.zero_not_one quotient_of_Fract 
      by auto
    moreover have \<open>quotient_of (1/x) = (v, u)\<close>
    proof-
      have \<open>1/x = Fract v u\<close>
        using \<open>x = Fract u v\<close>
        by (simp add: One_rat_def)
      moreover have \<open>gcd v u = 1\<close>
        using  \<open>gcd u v = 1\<close>
        by (simp add: gcd.commute)
      ultimately show ?thesis
        unfolding quotient_of_def
        using \<open>u > 0\<close> quotient_of_Fract quotient_of_def 
        by auto
    qed
    ultimately show ?thesis
      by auto
  next
    case False
    hence \<open>x < 0\<close>
      using \<open>x \<noteq> 0\<close> 
      by simp
    hence \<open>\<exists> u v. x = Fract u v \<and> gcd u v = 1 \<and> u < 0 \<and> v > 0\<close>
      using \<open>x \<noteq> 0\<close> Rat_cases_nonzero coprime_imp_gcd_eq_1 zero_less_Fract_iff
    proof -
      have "\<forall>r. \<exists>i ia. x \<noteq> 0 \<and> 0 < i \<and> (r = 0 \<or> coprime ia i) \<and> (r = 0 \<or> Fract ia i = r)"
        by (metis (full_types) Rat_cases_nonzero \<open>x \<noteq> 0\<close>)
      then show ?thesis
        by (metis (no_types) Fract_less_zero_iff \<open>x < 0\<close> coprime_imp_gcd_eq_1)
    qed
    then obtain u v where \<open>x = Fract u v\<close> and \<open>gcd u v = 1\<close> and \<open>u < 0\<close> and \<open>v > 0\<close>
      by auto
    have \<open>quotient_of x = (u, v)\<close>
      using \<open>0 < v\<close> \<open>gcd u v = 1\<close> \<open>x = Fract u v\<close> int.zero_not_one quotient_of_Fract 
      by auto
    moreover have \<open>quotient_of (1/x) = (-v, -u)\<close>
    proof-
      have \<open>1/x = Fract (-v) (-u)\<close>
        using \<open>x = Fract u v\<close>
        by (simp add: One_rat_def)
      moreover have \<open>gcd (-v) (-u) = 1\<close>
        using  \<open>gcd u v = 1\<close>
        by (simp add: gcd.commute)
      moreover have \<open>-u > 0\<close>
        using \<open>u < 0\<close>
        by simp
      ultimately show ?thesis
        unfolding quotient_of_def
        using quotient_of_Fract quotient_of_def 
        by auto
    qed
    ultimately show ?thesis
      by auto
  qed
qed


lemma multiplicity_quotient_snd: 
  \<open>multiplicity (int p) (snd (quotient_of (1 / x)))
                = multiplicity (int p) (fst (quotient_of x))\<close>
proof(cases \<open>x = 0\<close>)
  case True
  thus ?thesis
    by (simp add: True) 
next
  case False
  hence \<open>x \<noteq> 0\<close>
    by blast
  show ?thesis 
  proof(cases \<open>x > 0\<close>)
    case True
    hence \<open>\<exists> u v. x = Fract u v \<and> gcd u v = 1 \<and> u > 0 \<and> v > 0\<close>
      by (metis \<open>x \<noteq> 0\<close> Rat_cases_nonzero coprime_imp_gcd_eq_1 zero_less_Fract_iff)
    then obtain u v where \<open>x = Fract u v\<close> and \<open>gcd u v = 1\<close> and \<open>u > 0\<close> and \<open>v > 0\<close>
      by auto
    have \<open>quotient_of x = (u, v)\<close>
      using \<open>0 < v\<close> \<open>gcd u v = 1\<close> \<open>x = Fract u v\<close> int.zero_not_one quotient_of_Fract 
      by auto
    moreover have \<open>quotient_of (1/x) = (v, u)\<close>
    proof-
      have \<open>1/x = Fract v u\<close>
        using \<open>x = Fract u v\<close>
        by (simp add: One_rat_def)
      moreover have \<open>gcd v u = 1\<close>
        using  \<open>gcd u v = 1\<close>
        by (simp add: gcd.commute)
      ultimately show ?thesis
        unfolding quotient_of_def
        using \<open>u > 0\<close> quotient_of_Fract quotient_of_def 
        by auto
    qed
    ultimately show ?thesis
      by auto
  next
    case False
    hence \<open>x < 0\<close>
      using \<open>x \<noteq> 0\<close> 
      by simp
    hence \<open>\<exists> u v. x = Fract u v \<and> gcd u v = 1 \<and> u < 0 \<and> v > 0\<close>
      using \<open>x \<noteq> 0\<close> Rat_cases_nonzero coprime_imp_gcd_eq_1 zero_less_Fract_iff
    proof -
      have "\<forall>r. \<exists>i ia. x \<noteq> 0 \<and> 0 < i \<and> (r = 0 \<or> coprime ia i) \<and> (r = 0 \<or> Fract ia i = r)"
        by (metis (full_types) Rat_cases_nonzero \<open>x \<noteq> 0\<close>)
      then show ?thesis
        by (metis (no_types) Fract_less_zero_iff \<open>x < 0\<close> coprime_imp_gcd_eq_1)
    qed
    then obtain u v where \<open>x = Fract u v\<close> and \<open>gcd u v = 1\<close> and \<open>u < 0\<close> and \<open>v > 0\<close>
      by auto
    have \<open>quotient_of x = (u, v)\<close>
      using \<open>0 < v\<close> \<open>gcd u v = 1\<close> \<open>x = Fract u v\<close> int.zero_not_one quotient_of_Fract 
      by auto
    moreover have \<open>quotient_of (1/x) = (-v, -u)\<close>
    proof-
      have \<open>1/x = Fract (-v) (-u)\<close>
        using \<open>x = Fract u v\<close>
        by (simp add: One_rat_def)
      moreover have \<open>gcd (-v) (-u) = 1\<close>
        using  \<open>gcd u v = 1\<close>
        by (simp add: gcd.commute)
      moreover have \<open>-u > 0\<close>
        using \<open>u < 0\<close>
        by simp
      ultimately show ?thesis
        unfolding quotient_of_def
        using quotient_of_Fract quotient_of_def 
        by auto
    qed
    ultimately show ?thesis
      by auto
  qed
qed

lemma pval_inverse:
  \<open>prime p \<Longrightarrow> pval p (1/x) = - pval p x\<close>
proof-
  assume \<open>prime p\<close>
  have \<open>pval p (1/x) = int (multiplicity (int p) (fst (quotient_of (1 / x)))) -
    int (multiplicity (int p) (snd (quotient_of (1 / x))))\<close>
    unfolding pval_def
    by blast
  also have \<open>\<dots> = int (multiplicity (int p) (snd (quotient_of x))) -
    int (multiplicity (int p) (fst (quotient_of x)))\<close>
  proof-
    have \<open>(multiplicity (int p) (fst (quotient_of (1 / x)))) 
        = (multiplicity (int p) (snd (quotient_of x)))\<close>
      by (simp add: multiplicity_quotient_fst)      
    moreover have \<open>multiplicity (int p) (snd (quotient_of (1 / x)))
                = multiplicity (int p) (fst (quotient_of x))\<close>
      by (simp add: multiplicity_quotient_snd)      
    ultimately show ?thesis 
      by simp
  qed
  also have \<open>\<dots> = - (pval p x)\<close>
    unfolding pval_def 
    by simp
  finally show ?thesis
    by blast
qed

lemma pval_uniq':
  \<open>prime p \<Longrightarrow> y \<noteq> 0 \<Longrightarrow> x = (p powr (of_int l)) * y \<Longrightarrow> pval p y = 0 \<Longrightarrow> l \<ge> 0 \<Longrightarrow> pval p x = l\<close>
proof-
  assume \<open>prime p\<close> and \<open>y \<noteq> 0\<close> and \<open>x = (p powr (of_int l)) * y\<close> and \<open>pval p y = 0\<close> and  \<open>l \<ge> 0\<close>
  have \<open>y = Fract (fst (quotient_of y)) (snd (quotient_of y))\<close>
    by (simp add: Fract_of_int_quotient quotient_of_div)
  have \<open>p > 0\<close>
    using \<open>prime p\<close>
    by (simp add: prime_gt_0_nat)
  have \<open>x = p^(nat l) * y\<close>
  proof-
    have \<open>p powr (of_int l) =  p^(nat l)\<close>
      using \<open>l \<ge> 0\<close> Transcendental.powr_realpow[where x = p and n = "nat l"]  \<open>p > 0\<close>
      by simp
    thus ?thesis
      by (simp add: \<open>of_rat x = complex_of_real (real p powr real_of_int l) * of_rat y\<close>)
  qed
  also have \<open>\<dots> = p^(nat l) * Fract (fst (quotient_of y)) (snd (quotient_of y))\<close>
    using \<open>y = Fract (fst (quotient_of y)) (snd (quotient_of y))\<close>
    by simp      
  also have \<open>\<dots> = (Fract (p^(nat l)) 1) * (Fract ((fst (quotient_of y))) (snd (quotient_of y)))\<close>
  proof-
    have \<open>p^(nat l) = Fract (p^(nat l)) 1\<close>
      by (metis Fract_of_nat_eq of_rat_of_nat_eq)        
    thus ?thesis
      by (metis of_rat_mult)        
  qed
  also have \<open>\<dots> = Fract (p^(nat l) * (fst (quotient_of y))) (snd (quotient_of y))\<close>
    by simp
  finally have \<open>x = (Fract ((p ^ nat l) * fst (quotient_of y)) (snd (quotient_of y)))\<close>
    by simp
  moreover have \<open>coprime ((p ^ nat l) * fst (quotient_of y)) (snd (quotient_of y))\<close>
  proof-
    have \<open>coprime (fst (quotient_of y)) (snd (quotient_of y))\<close>
      by (simp add: quotient_of_coprime)
    moreover have \<open>coprime (p ^ nat l) (snd (quotient_of y))\<close>
      by (metis Fract_less_zero_iff \<open>prime p\<close> \<open>pval p y = 0\<close> \<open>y = Fract (fst (quotient_of y)) 
          (snd (quotient_of y))\<close> calculation coprime_absorb_left coprime_commute
          coprime_power_left_iff dvd_0_right int.lless_eq is_unit_right_imp_coprime nat_0_iff 
          neq0_conv of_nat_power prime_imp_coprime_int prime_nat_int_transfer pval_unit_dvd 
          quotient_of_denom_pos' zero_less_Fract_iff zero_less_nat_eq)
    ultimately show ?thesis
      using coprime_mult_left_iff 
      by blast 
  qed
  moreover have \<open>snd (quotient_of y) > 0\<close>
    by (simp add: quotient_of_denom_pos')
  ultimately have \<open>quotient_of x = ((p^(nat l)) * fst (quotient_of y), snd (quotient_of y))\<close>
    by (simp add: quotient_of_Fract)
  have \<open>pval p x = int (multiplicity p (fst (quotient_of x)) )
                   - int (multiplicity p (snd (quotient_of x)) )\<close>
    unfolding pval_def 
    by blast
  also have \<open>\<dots> = int (multiplicity p ((p^(nat l)) * fst (quotient_of y)) )
                  - int (multiplicity p (snd (quotient_of y)) )\<close>
    using \<open>quotient_of x = ((p^(nat l)) * fst (quotient_of y), snd (quotient_of y))\<close>
    by simp
  also have \<open>\<dots> = int (multiplicity p ((p^(nat l)) * fst (quotient_of y)) )\<close>
  proof-
    have \<open>multiplicity p (snd (quotient_of y)) = 0\<close>
      by (metis \<open>prime p\<close> \<open>pval p y = 0\<close> dvd_refl multiplicity_unit_right 
          not_dvd_imp_multiplicity_0 pval_unit_dvd rat_zero_code snd_conv)        
    thus ?thesis 
      by simp
  qed
  also have \<open>\<dots> = l\<close>
  proof-
    have \<open>l \<le> multiplicity  p ((p ^ nat l) * fst (quotient_of y))\<close>
    proof-
      have \<open>(p ^ nat l) * fst (quotient_of y) \<noteq> 0\<close>
      proof-
        have \<open>p ^ nat l \<noteq> 0\<close>
          using \<open>prime p\<close>
          by auto
        moreover have \<open>fst (quotient_of y) \<noteq> 0\<close>
          using \<open>y \<noteq> 0\<close>
          by (metis Zero_rat_def \<open>y = Fract (fst (quotient_of y)) (snd (quotient_of y))\<close> eq_rat(3))
        ultimately show ?thesis 
          by simp
      qed
      moreover have \<open>(p ^ nat l) dvd ((p ^ nat l) * fst (quotient_of y))\<close>
        by simp          
      moreover have \<open>\<not> is_unit (int p)\<close>
        using \<open>prime p\<close>
        by auto
      ultimately show ?thesis 
        using multiplicity_geI[where x = "(p ^ nat l) * fst (quotient_of y)" 
            and p = p and n = "nat l"]
        by simp
    qed
    moreover have \<open>multiplicity p ((p ^ nat l) * fst (quotient_of y)) < l + 1\<close>
    proof(rule classical)
      assume \<open>\<not> (multiplicity p ((p ^ nat l) * fst (quotient_of y)) < l + 1)\<close>
      hence \<open>multiplicity p ((p ^ nat l) * fst (quotient_of y)) \<ge> l + 1\<close>
        by simp
      hence \<open>(p ^ (nat l+1)) dvd ((p ^ nat l) * fst (quotient_of y))\<close>
        using multiplicity_dvd'[where n = "nat l + 1" and p = p 
            and x = "(p ^ nat l) * fst (quotient_of y)"] \<open>l \<ge> 0\<close> 
        by auto
      hence \<open>((p ^ nat l)*p) dvd ((p ^ nat l) * fst (quotient_of y))\<close>
        by simp
      hence \<open>p dvd (fst (quotient_of y))\<close>
        using \<open>prime p\<close> 
        by auto
      thus ?thesis
        using \<open>prime p\<close> \<open>pval p y = 0\<close> \<open>y \<noteq> 0\<close> pval_unit_dvd 
        by blast 
    qed
    ultimately show ?thesis 
      by simp
  qed
  finally show ?thesis
    by simp 
qed


lemma pval_uniq:
  \<open>prime p \<Longrightarrow> y \<noteq> 0 \<Longrightarrow> x = (p powr (of_int l)) * y \<Longrightarrow> pval p y = 0 \<Longrightarrow> pval p x = l\<close>
proof-
  assume \<open>prime p\<close> and \<open>y \<noteq> 0\<close> and \<open>x = (p powr (of_int l)) * y\<close> and \<open>pval p y = 0\<close>
  show ?thesis
  proof(cases \<open>l \<ge> 0\<close>)
    case True
    thus ?thesis
      using \<open>of_rat x = complex_of_real (real p powr real_of_int l) * of_rat y\<close> \<open>prime p\<close> 
        \<open>pval p y = 0\<close> \<open>y \<noteq> 0\<close> pval_uniq' 
      by blast 
  next
    case False
    define l' where \<open>l' = -l\<close>
    have \<open>l' \<ge> 0\<close>
      using False l'_def 
      by linarith
    define x' where \<open>x' = 1/x\<close>
    define y' where \<open>y' = 1/y\<close>
    have \<open>y' \<noteq> 0\<close>
      unfolding y'_def
      by (simp add: \<open>y \<noteq> 0\<close>)
    moreover have \<open>x' = (p powr (of_int l')) * y'\<close>
    proof-
      have \<open>x' = 1/((p powr (of_int l)) * y)\<close>
        unfolding  x'_def
        using \<open>x = (p powr (of_int l)) * y\<close>
        by (simp add: of_rat_divide)
      also have \<open>\<dots> = (1/(p powr (of_int l)))*(1/y)\<close>
        by (simp add: \<open>y \<noteq> 0\<close> nonzero_of_rat_divide)
      also have \<open>\<dots> = (1/(p powr (of_int l)))*y'\<close>
        unfolding y'_def
        by simp
      also have \<open>\<dots> = (p powr (- of_int l))*y'\<close>
        by (simp add: divide_powr_uminus)
      also have \<open>\<dots> = (p powr (of_int l'))*y'\<close>
        unfolding l'_def
        by simp
      finally show ?thesis
        by blast
    qed
    moreover have  \<open>pval p y' = 0\<close>
      unfolding y'_def
      by (simp add: \<open>prime p\<close> \<open>pval p y = 0\<close> pval_inverse)
    ultimately have \<open>pval p x' = l'\<close>
      using \<open>0 \<le> l'\<close> \<open>prime p\<close> pval_uniq' 
      by blast
    thus \<open>pval p x = l\<close>
      unfolding x'_def l'_def
      using \<open>prime p\<close> pval_inverse 
      by simp
  qed
qed

lemma pval_zero: \<open>prime p \<Longrightarrow> pval p 0 = 0\<close>
proof-
  assume \<open>prime p\<close>
  have \<open>quotient_of 0 = (0, 1)\<close>
    by simp
  thus ?thesis
    unfolding pval_def
    by auto
qed

lemma pval_comprime:
  \<open>prime p \<Longrightarrow> \<not> ( p dvd (fst (quotient_of x)) ) \<or>  \<not> ( p dvd (snd (quotient_of x)) )\<close>
proof-
  assume \<open>prime p\<close>
  show ?thesis
  proof(rule classical)
    assume \<open>\<not>(\<not> ( p dvd (fst (quotient_of x)) ) \<or>  \<not> ( p dvd (snd (quotient_of x)) ))\<close>
    hence \<open>p dvd (fst (quotient_of x)) \<and> p dvd (snd (quotient_of x))\<close>
      by blast
    hence \<open>\<not> coprime (fst (quotient_of x)) (snd (quotient_of x))\<close>
      using \<open>prime p\<close> coprime_common_divisor not_prime_unit 
      by blast
    thus ?thesis
      using quotient_of_coprime 
      by auto 
  qed
qed

lemma pval_decomposition:
  \<open>prime p \<Longrightarrow> \<exists> y. (x::rat) = (p powr (of_int (pval p x))) * y \<and> pval p y = 0\<close>
proof(cases \<open>x = 0\<close>)
  case True
  assume \<open>prime p\<close>
  define y::rat where \<open>y = 0\<close>
  have \<open>x = (p powr (of_int (pval p x))) * y\<close> 
    unfolding y_def
    by (simp add: True)    
  moreover  have \<open>pval p y = 0\<close>
    unfolding y_def
    using pval_zero \<open>prime p\<close>
    by simp
  ultimately show ?thesis 
    by blast
next
  case False
  assume \<open>prime p\<close>
  hence \<open>\<not> ( p dvd (fst (quotient_of x)) ) \<or>  \<not> ( p dvd (snd (quotient_of x)) )\<close>
    using prime_nat_int_transfer pval_comprime 
    by blast    
  show ?thesis
  proof(cases \<open>\<not> ( p dvd (snd (quotient_of x)) )\<close>)
    case True
    hence \<open>multiplicity p (snd (quotient_of x)) = 0\<close>
      using not_dvd_imp_multiplicity_0 
      by auto
    hence \<open>pval p x = int (multiplicity (int p) (fst (quotient_of x))) -
    int (multiplicity (int p) (snd (quotient_of x)))\<close>
      unfolding pval_def
      by blast
    also have \<open>\<dots> = (multiplicity (int p) (fst (quotient_of x)))\<close>
      by (simp add: \<open>multiplicity (int p) (snd (quotient_of x)) = 0\<close>)
    finally have \<open>pval p x = multiplicity (int p) (fst (quotient_of x))\<close>
      by blast
    hence \<open>pval p x \<ge> 0\<close>
      by simp      
    have \<open>(p ^ (nat (pval p x))) dvd fst (quotient_of x)\<close>
      using multiplicity_dvd \<open>pval p x = multiplicity (int p) (fst (quotient_of x))\<close>
      by simp
    hence \<open>\<exists> k::int. fst (quotient_of x) = p ^ (nat (pval p x)) * k\<close>
      by auto
    then obtain k::int where \<open>fst (quotient_of x) = p ^ (nat (pval p x)) * k\<close>
      by blast
    have \<open>multiplicity p k = 0\<close>
    proof(rule classical)
      assume \<open>\<not> (multiplicity p k = 0)\<close>
      hence \<open>multiplicity p k \<ge> 1\<close>
        by auto
      hence \<open>p dvd k\<close>
        by (meson \<open>multiplicity (int p) k \<noteq> 0\<close> not_dvd_imp_multiplicity_0)
      hence \<open>(p ^ (nat (pval p x)+1)) dvd (p ^ (nat (pval p x))*k)\<close>
        by simp
      hence \<open>(p ^ (nat (pval p x)+1)) dvd (fst (quotient_of x))\<close>
        by (simp add: \<open>fst (quotient_of x) = int (p ^ nat (pval p x)) * k\<close>)
      hence \<open>multiplicity p (fst (quotient_of x)) \<ge> nat (pval p x)+1\<close>
        using multiplicity_geI
        by (metis \<open>fst (quotient_of x) = int (p ^ nat (pval p x)) * k\<close> \<open>multiplicity (int p) k \<noteq> 0\<close> \<open>prime p\<close> multiplicity_unit_left multiplicity_zero no_zero_divisors not_prime_0 of_nat_eq_0_iff of_nat_power power_not_zero)
      thus ?thesis
        by (simp add: \<open>pval p x = int (multiplicity (int p) (fst (quotient_of x)))\<close>)
    qed
    define y where \<open>y = Fract k (snd (quotient_of x))\<close>
    have \<open>pval p y = 0\<close>
    proof-
      have \<open>coprime k (snd (quotient_of x))\<close>
        by (metis \<open>fst (quotient_of x) = int (p ^ nat (pval p x)) * k\<close> coprime_mult_left_iff 
            prod.exhaust_sel quotient_of_coprime)        
      hence \<open>quotient_of y = (k, snd (quotient_of x))\<close>
        by (simp add: quotient_of_Fract quotient_of_denom_pos' y_def)
      have \<open>pval p y =  int (multiplicity (int p) (fst (quotient_of y))) -
                        int (multiplicity (int p) (snd (quotient_of y)))\<close>
        unfolding pval_def
        by blast
      moreover have \<open>multiplicity (int p) (fst (quotient_of y)) = 0\<close>
        unfolding y_def
        using \<open>multiplicity p k = 0\<close> \<open>quotient_of y = (k, snd (quotient_of x))\<close> y_def 
        by auto        
      moreover have \<open>multiplicity (int p) (snd (quotient_of y)) = 0\<close>
        unfolding y_def
        using \<open>multiplicity (int p) (snd (quotient_of x)) = 0\<close>
          \<open>quotient_of y = (k, snd (quotient_of x))\<close> y_def 
        by auto
      ultimately show ?thesis
        by simp
    qed
    have \<open>x = (fst (quotient_of x))/ (snd (quotient_of x))\<close>
      by (metis (mono_tags, lifting) of_rat_divide of_rat_of_int_eq of_real_divide of_real_of_int_eq
          quotient_of_div surjective_pairing)
    also have \<open>\<dots> = (p ^ (nat (pval p x)) * k)/ (snd (quotient_of x))\<close>
      by (simp add: \<open>fst (quotient_of x) = int (p ^ nat (pval p x)) * k\<close>)
    also have \<open>\<dots> = p ^ (nat (pval p x)) * (k/ (snd (quotient_of x)))\<close>
      by simp
    also have \<open>\<dots> = p ^ (nat (pval p x)) * y\<close>
      unfolding y_def
      by (metis True dvd_0_right of_rat_rat of_real_divide of_real_mult of_real_of_int_eq 
          of_real_of_nat_eq)      
    finally have \<open>x = p ^ (nat (pval p x)) * y\<close>
      by blast
    moreover have \<open>p powr (of_int (pval p x)) = p ^ (nat (pval p x))\<close>
      using \<open>pval p x \<ge> 0\<close>
      by (metis \<open>prime p\<close> of_nat_0_less_iff of_nat_nat of_nat_power powr_realpow prime_gt_0_nat) 
    ultimately have \<open>x = (p powr (of_int (pval p x))) * y\<close>
      by simp
    thus ?thesis
      using \<open>pval p y = 0\<close>
      by blast
  next
    case False
    hence \<open>\<not> ( p dvd (fst (quotient_of x)) )\<close>
      using \<open>\<not> int p dvd fst (quotient_of x) \<or> \<not> int p dvd snd (quotient_of x)\<close>
      by auto      
    hence \<open>multiplicity p (fst (quotient_of x)) = 0\<close>
      using not_dvd_imp_multiplicity_0 
      by auto
    hence \<open>pval p x = int (multiplicity (int p) (fst (quotient_of x))) -
    int (multiplicity (int p) (snd (quotient_of x)))\<close>
      unfolding pval_def
      by blast
    also have \<open>\<dots> = -(multiplicity (int p) (snd (quotient_of x)))\<close>
      by (simp add: \<open>multiplicity (int p) (fst (quotient_of x)) = 0\<close>)
    finally have \<open>pval p x = -multiplicity (int p) (snd (quotient_of x))\<close>
      by blast
    hence \<open>pval p x \<le> 0\<close>
      by simp      
    have \<open>(p ^ (nat (-pval p x))) dvd snd (quotient_of x)\<close>
      using multiplicity_dvd
      by (simp add: multiplicity_dvd \<open>pval p x = - int (multiplicity (int p) (snd (quotient_of x)))\<close>) 
    hence \<open>\<exists> k::int. snd (quotient_of x) = p ^ (nat (-pval p x)) * k\<close>
      by auto
    then obtain k::int where \<open>snd (quotient_of x) = p ^ (nat (-pval p x)) * k\<close>
      by blast
    have \<open>multiplicity p k = 0\<close>
    proof(rule classical)
      assume \<open>\<not> (multiplicity p k = 0)\<close>
      hence \<open>multiplicity p k \<ge> 1\<close>
        by auto
      hence \<open>p dvd k\<close>
        by (meson \<open>multiplicity (int p) k \<noteq> 0\<close> not_dvd_imp_multiplicity_0)
      hence \<open>(p ^ (nat (-pval p x)+1)) dvd (p ^ (nat (-pval p x))*k)\<close>
        by simp
      hence \<open>(p ^ (nat (-pval p x)+1)) dvd (snd (quotient_of x))\<close>
        by (simp add: \<open>snd (quotient_of x) = int (p ^ nat (- pval p x)) * k\<close>)
      hence \<open>multiplicity p (snd (quotient_of x)) \<ge> nat (-pval p x)+1\<close>
        using multiplicity_geI \<open>1 \<le> multiplicity (int p) k\<close> \<open>pval p x \<le> 0\<close>
        by (metis \<open>multiplicity (int p) k \<noteq> 0\<close> \<open>prime p\<close>
            \<open>snd (quotient_of x) = int (p ^ nat (- pval p x)) * k\<close> divisors_zero 
            multiplicity_unit_left multiplicity_zero not_prime_0 of_nat_eq_0_iff of_nat_power 
            power_not_zero) 
      thus ?thesis
        by (simp add: \<open>pval p x = - int (multiplicity (int p) (snd (quotient_of x)))\<close>)        
    qed
    define y where \<open>y = Fract (fst (quotient_of x)) k\<close>
    have \<open>pval p y = 0\<close>
    proof-
      have \<open>coprime (fst (quotient_of x)) k\<close>
        by (metis \<open>snd (quotient_of x) = int (p ^ nat (- pval p x)) * k\<close> coprime_mult_right_iff 
            prod.collapse quotient_of_coprime)
      moreover have \<open>k > 0\<close>
      proof-
        have \<open>snd (quotient_of x) > 0\<close>
          by (simp add: quotient_of_denom_pos')
        thus ?thesis
          using  \<open>snd (quotient_of x) = int (p ^ nat (- pval p x)) * k\<close>
          by (simp add: zero_less_mult_iff)
      qed
      ultimately have \<open>quotient_of y = (fst (quotient_of x), k)\<close>
        unfolding y_def
        by (simp add: quotient_of_Fract)          
      have \<open>pval p y =  int (multiplicity (int p) (fst (quotient_of y))) -
                        int (multiplicity (int p) (snd (quotient_of y)))\<close>
        unfolding pval_def
        by blast
      moreover have \<open>multiplicity (int p) (fst (quotient_of y)) = 0\<close>
        unfolding y_def
        using \<open>multiplicity (int p) (fst (quotient_of x)) = 0\<close> 
          \<open>quotient_of y = (fst (quotient_of x), k)\<close> y_def 
        by auto
      moreover have \<open>multiplicity (int p) (snd (quotient_of y)) = 0\<close>
        unfolding y_def
        using \<open>multiplicity (int p) k = 0\<close> \<open>quotient_of y = (fst (quotient_of x), k)\<close> y_def 
        by auto
      ultimately show ?thesis
        by simp
    qed
    have \<open>x = (fst (quotient_of x))/ (snd (quotient_of x))\<close>
      by (metis (mono_tags, lifting) of_rat_divide of_rat_of_int_eq of_real_divide of_real_of_int_eq
          quotient_of_div surjective_pairing)
    also have \<open>\<dots> = (fst (quotient_of x))/(p ^ (nat (-pval p x)) * k)\<close>
      by (simp add: \<open>snd (quotient_of x) = int (p ^ nat (- pval p x)) * k\<close>)      
    also have \<open>\<dots> = (1/(p ^ (nat (-pval p x)))) * ((fst (quotient_of x))/k)\<close>
      by simp
    also have \<open>\<dots> = (1/(p ^ (nat (-pval p x)))) * y\<close>
    proof-
      have \<open>Fract (fst (quotient_of x)) k = (fst (quotient_of x))/k\<close>
        by (metis (no_types, hide_lams) division_ring_divide_zero of_int_0_eq_iff of_rat_0 
            of_rat_rat of_real_divide of_real_of_int_eq rat_number_collapse(6))
      thus ?thesis
        unfolding y_def
        by simp
    qed
    finally have \<open>x = (1/(p ^ (nat (-pval p x)))) * y\<close>
      by blast
    moreover have \<open>p powr (of_int (pval p x)) = 1/(p ^ (nat (-pval p x)))\<close>
      using \<open>pval p x \<le> 0\<close>
        \<open>prime p\<close> div_by_1 nat_0_iff not_prime_0 of_nat_le_0_iff of_nat_power power_0 powr_int
    proof -
      have "p \<noteq> 0"
        by (metis \<open>prime p\<close> not_prime_0)
      then have "\<not> int p \<le> 0"
        by auto
      then have "\<not> real p \<le> 0"
        by auto
      then show ?thesis
        by (simp add: \<open>pval p x \<le> 0\<close> powr_int)
    qed   
    ultimately have \<open>x = (p powr (of_int (pval p x))) * y\<close>
      by simp
    thus ?thesis
      using \<open>pval p y = 0\<close>
      by blast
  qed
qed

lemma pval_additivity:
  \<open>prime p \<Longrightarrow> u \<noteq> 0 \<Longrightarrow> v \<noteq> 0 \<Longrightarrow> pval p (u * v) = (pval p u) + (pval p v)\<close>
proof-
  assume \<open>prime p\<close> and \<open>u \<noteq> 0\<close> and \<open>v \<noteq> 0\<close>
  hence \<open>\<exists> y. u = ((of_int p) powr (of_int (pval p u))) * y \<and> pval p y = 0\<close>
    using pval_decomposition[where p = "p" and x = "u"]
    by simp
  then obtain yu where \<open>u = ((of_int p) powr (of_int (pval p u))) * yu\<close> and \<open>pval p yu = 0\<close>
    by blast
  have \<open>\<exists> y. v = ((of_int p) powr (of_int (pval p v))) * y \<and> pval p y = 0\<close>
    using pval_decomposition[where p = "p" and x = "v"] \<open>prime p\<close>
    by simp
  then obtain yv where \<open>v = ((of_int p) powr (of_int (pval p v))) * yv\<close> and \<open>pval p yv = 0\<close>
    by blast
  have \<open>u * v = ( ((of_int p) powr (of_int (pval p u))) * ((of_int p) powr (of_int (pval p v))) ) 
                 * (yu * yv)\<close> 
    using \<open>u = ((of_int p) powr (of_int (pval p u))) * yu\<close>
      \<open>v = ((of_int p) powr (of_int (pval p v))) * yv\<close>
    by (simp add: of_rat_mult)
  also have  \<open>\<dots> = ( ((of_int p) powr (of_int (pval p u + pval p v)) )  ) 
                 * (yu * yv)\<close> 
  proof-
    have \<open>real_of_int (int p) powr real_of_int (pval p u) 
    * real_of_int (int p) powr real_of_int (pval p v) 
    = real_of_int (int p) powr (real_of_int (pval p u) + real_of_int (pval p v))\<close>
      using Transcendental.powr_add[where x = "((of_int p)::real)" 
          and a = "(of_int (pval p u))::real" 
          and b = "(of_int (pval p v))::real"]
      by auto
    moreover have \<open>real_of_int (pval p u + pval p v) = real_of_int (pval p u) + real_of_int (pval p v)\<close>
      by auto
    ultimately have \<open>((of_int p) powr (of_int (pval p u))) * ((of_int p) powr (of_int (pval p v)))
          = (of_int p) powr (real_of_int (pval p u + pval p v)) \<close>
      by auto
    thus ?thesis
      by (metis (no_types) \<open>of_int (int p) powr of_int (pval p u) * of_int (int p) powr 
        of_int (pval p v) = of_int (int p) powr of_int (pval p u + pval p v)\<close> of_real_mult)
  qed
  finally have \<open>u * v =
  complex_of_real (real_of_int (int p) powr real_of_int (pval p u + pval p v)) *
  of_rat (yu * yv)\<close>
    by blast
  moreover have \<open>pval p (yu * yv) = 0\<close>
    using pval_composition_of_units \<open>prime p\<close> \<open>pval p yu = 0\<close> \<open>pval p yv = 0\<close>
    by (metis mult_eq_0_iff)        
  ultimately show ?thesis
    using pval_uniq[where p = "p" and x = "u * v" and l = "pval p u + pval p v" and y = "yu * yv"]
      \<open>prime p\<close> \<open>u \<noteq> 0\<close> \<open>v \<noteq> 0\<close> 
    by force 
qed

lemma pval_primepow:
  \<open>prime p \<Longrightarrow> pval p ((of_int p)^l) = l\<close>
proof-
  assume \<open>prime p\<close>
  define x where \<open>x = Fract (p^l) 1\<close>
  have \<open>quotient_of x = (p^l, 1)\<close>
  proof-
    have \<open>coprime (p^l) 1\<close>
      by simp      
    thus ?thesis 
      unfolding x_def
      by (simp add: quotient_of_Fract)      
  qed
  have \<open>int (multiplicity p (fst (quotient_of x)) ) = l\<close>
  proof-
    have \<open>fst (quotient_of x) = p^l\<close>
      by (simp add: \<open>quotient_of x = (case (p ^ l, 1) of (x, y) \<Rightarrow> (int x, y))\<close>)
    thus ?thesis 
      by (simp add: \<open>prime p\<close>)
  qed
  moreover have \<open>int (multiplicity p  (snd (quotient_of x)) ) = 0\<close>
  proof-
    have \<open>snd (quotient_of x) = 1\<close>
      by (simp add: \<open>quotient_of x = (case (p ^ l, 1) of (x, y) \<Rightarrow> (int x, y))\<close>)
    thus ?thesis 
      by (simp add: \<open>prime p\<close>)
  qed
  moreover have \<open>x = (of_int p)^l\<close>
    by (metis Fract_of_nat_eq of_int_of_nat_eq of_nat_power x_def)    
  ultimately show ?thesis 
    unfolding pval_def
    by simp
qed

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

lemma pnorm_multiplicativity:
  \<open>prime p \<Longrightarrow> pnorm p (u * v) = (pnorm p u) * (pnorm p v)\<close>
proof(cases \<open>u * v = 0\<close>)
  case True
  hence \<open>u = 0 \<or> v = 0\<close>
    by (simp add: True divisors_zero)
  have \<open>pnorm p (u * v) = 0\<close>
    unfolding pnorm_def
    by (simp add: True)
  show ?thesis
  proof(cases \<open>u = 0\<close>)
    case True
    hence \<open>pnorm p u = 0\<close>
      unfolding pnorm_def
      by auto
    thus ?thesis
      by (simp add: \<open>pnorm p (u * v) = 0\<close>)
  next
    case False
    hence \<open>v = 0\<close>
      using \<open>u = 0 \<or> v = 0\<close> 
      by blast
    hence \<open>pnorm p v = 0\<close>
      unfolding pnorm_def
      by auto
    thus ?thesis
      by (simp add: \<open>pnorm p (u * v) = 0\<close>)
  qed
next
  case False
  hence \<open>u \<noteq> 0\<close>
    by simp
  hence \<open>v \<noteq> 0\<close>
    using False
    by simp
  assume \<open>prime p\<close>
  have \<open>pnorm p (u * v) = p powr (-(pval p (u * v)))\<close>
    using pnorm_simplified[where p = "p" and x = "u * v"]
      False by blast    
  also have \<open>\<dots> = p powr (-(pval p u) - (pval p v))\<close>
  proof-
    have \<open>pval p (u * v) = (pval p u) + (pval p v)\<close>
      using \<open>u \<noteq> 0\<close> \<open>v \<noteq> 0\<close>  \<open>prime p\<close> pval_additivity[where p = "p" and u = "u" and v = "v"]
      by blast
    hence \<open>-(pval p (u * v)) = -(pval p u) - (pval p v)\<close>
      by simp
    thus ?thesis
      by simp 
  qed
  also have \<open>\<dots> = (p powr (-(pval p u)))*(p powr (- (pval p v)))\<close>
    by (metis linordered_field_class.sign_simps(2) of_int_add powr_add uminus_add_conv_diff)    
  also have \<open>\<dots> = (pnorm p u)*(pnorm p v)\<close>
    using \<open>u \<noteq> 0\<close> \<open>v \<noteq> 0\<close> pnorm_simplified 
    by auto
  finally show ?thesis by blast
qed

lemma pnorm_primepow:
  \<open>prime p \<Longrightarrow> pnorm p ((of_int p)^l) = 1/p^l\<close>
proof-
  assume \<open>prime p\<close>
  moreover have \<open>(of_int p)^l \<noteq> (0::rat)\<close>
    using calculation by auto
  ultimately have \<open>pnorm p ((of_int p)^l) = p powr  (- (pval p ((of_int p)^l)) )\<close>
    using pnorm_simplified 
    by auto
  moreover have \<open>pval p ((of_int p)^l) = l\<close>
    using pval_primepow \<open>prime p\<close>
    by auto
  ultimately have \<open>pnorm p ((of_int p)^l) = p powr (-l)\<close>
    by simp
  also have \<open>p powr (-l) = 1/p^l\<close>
    using Transcendental.powr_minus_divide[where x = "p" and a = "l"]
    by (simp add: \<open>prime p\<close> powr_realpow prime_gt_0_nat)
  finally show ?thesis 
    by simp
qed

subsection \<open>Auxiliary results\<close>
lemma harmonic_numbers_2norm:
  fixes n :: nat
  assumes \<open>n \<ge> 2\<close>
  shows \<open>pnorm 2 (\<Sum>k = 1..n. (Fract 1 (of_nat k))) = 2^(nat(\<lfloor>log 2 n\<rfloor>))\<close>
proof-
  define l where \<open>l = nat(\<lfloor>log 2 n\<rfloor>)\<close>
  define H where \<open>H = (\<Sum>k = 1..n. (Fract 1 (of_nat k)))\<close>
  have \<open>pnorm 2 ((2^l) * H) = 1\<close>
    sorry
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

