theory Utils
  imports
    "HOL.Map"
    "HOL-Library.Multiset"
    "Coinductive.Coinductive_List"
begin

definition
  map_plus :: "('a \<rightharpoonup> 'b::ab_semigroup_add) \<Rightarrow> ('a \<rightharpoonup> 'b) \<Rightarrow> ('a \<rightharpoonup> 'b)"  (infixl "+++" 100) where
  "m1 +++ m2 = (\<lambda>x. case m2 x of None \<Rightarrow> m1 x | Some y \<Rightarrow> (case m1 x of None \<Rightarrow> Some y | Some y' \<Rightarrow> Some (y + y')))"

lemma map_plus_empty[simp]: "m +++ Map.empty = m"
  by(simp add: map_plus_def)

lemma empty_map_plus[simp]: "Map.empty +++ m = m"
  by (rule ext) (simp add: map_plus_def split: option.split)

lemma map_plus_comm: "m1 +++ m2 = m2 +++ m1"
  apply (rule ext)
  apply (simp add: map_plus_def split: option.split)
  apply safe
  using add.commute by auto

lemma map_plus_assoc: "m1 +++ m2 +++ m3 = m1 +++ (m2 +++ m3)"
  apply (rule ext)
  apply (simp add: map_plus_def split: option.split)
  apply safe
  apply (simp add: ab_semigroup_add_class.add_ac(1))
  done

lemma map_plus_both_none: "(m1 +++ m2) a = None \<Longrightarrow> m1 a = None \<and> m2 a = None"
  apply (simp add: map_plus_def split: option.split)
  by (smt (verit, best) option.case_eq_if option.distinct(1))

lemma map_plus_update_to_left: "(m1 +++ m2) a = None \<Longrightarrow> (m1 +++ m2)(a \<mapsto> n) = m1(a \<mapsto> n) +++ m2"
  apply (rule ext)
  apply (simp add: map_plus_def split: option.split)
  apply safe
   apply force
  by (metis (no_types, lifting) is_none_simps(1) is_none_simps(2) option.case_eq_if)

lemma map_plus_update_to_right: "(m1 +++ m2) a = None \<Longrightarrow> (m1 +++ m2)(a \<mapsto> n) = m1 +++ m2 (a \<mapsto> n)"
  apply (rule ext)
  apply (simp add: map_plus_def split: option.split)
  apply safe
  by (metis (mono_tags, lifting) is_none_simps(1) is_none_simps(2) option.case_eq_if)

lemma count_list_remove1:
  "x \<in> set xs \<Longrightarrow> count_list (remove1 x xs) x = count_list xs x - 1"
  apply (induct xs arbitrary: x)
   apply simp
  apply simp
  apply safe
  by blast

lemma count_list_Cons_remove:
  "count_list (x # data1) x = count_list data2 x \<Longrightarrow> count_list data1 x = count_list (remove1 x data2) x"
  apply simp
  apply (subst count_list_remove1)
   apply (metis count_list_0_iff nat.simps(3))
  apply simp
  done

lemma count_list_imp_count_mset:
  "count_list data1 = count_list data2 \<Longrightarrow> count (mset data1) = count (mset data2)"
  apply (rule ext)
  subgoal for x
    apply (drule fun_cong[of _ _ x])
    apply (induct data1 arbitrary: data2 x)
     apply simp
     apply (simp add: count_list_0_iff)
    subgoal for a data1 data2 x
      apply (cases "a = x")
      subgoal
        apply hypsubst_thin
        by (smt (verit, ccfv_SIG) add_diff_cancel_right' add_mset_remove_trivial count_add_mset count_inI count_list.simps(2) count_list_0_iff count_list_remove1 count_mset_0_iff mset_remove1 multi_member_split)
      subgoal
        by simp
      done
    done
  done

lemma cons_append:
  "a # as = [a] @ as"
  by simp

lemma filter_neq_nil_iff:
  "\<exists> x \<in> set xs . P x \<Longrightarrow> filter P xs \<noteq> []"
  by (simp add: filter_empty_conv)

lemma map_neq_nil_iff:
  "xs \<noteq> [] \<Longrightarrow> map f xs \<noteq> []"
  by blast

lemma remdups_neq_nil_iff:
  "xs \<noteq> [] \<Longrightarrow> remdups xs \<noteq> []"
  using remdups_eq_nil_iff by blast

lemma not_lfinite_imp_not_lnull: "\<not> lfinite xs \<Longrightarrow> \<not> lnull xs"
  using lnull_imp_lfinite by blast

lemma drop_Suc':
  "drop (Suc n) xs = tl (drop n xs)"
  apply (induct xs arbitrary: n)
  by (simp_all add: tl_drop)

lemma last_sorted_is_Max:
  "xs \<noteq> [] \<Longrightarrow> sorted xs \<Longrightarrow> last xs = Max (set xs)"
  unfolding Max_def
  apply (induct xs)
   apply simp
  subgoal for a xs
    apply (subst List.semilattice_set.set_eq_fold)
    using Max.semilattice_set_axioms apply blast
    by (metis List.finite_set Max.semilattice_set_axioms Max.set_eq_fold Max_def fold_simps(1) last_ConsL last_ConsR last_in_set list.simps(15) max.absorb_iff2 semilattice_set.insert set_empty sorted_simps(2))
  done

lemma last_sort_is_Max:
  "xs \<noteq> [] \<Longrightarrow> last (sort xs) = Max (set xs)"
  apply (induct xs)
   apply simp
  subgoal for a xs
    using last_sorted_is_Max
    by (metis set_empty set_sort sorted_sort)
  done

lemma map_eq_set_D:
  "(map f xs = ys) \<Longrightarrow> x \<in> set ys \<Longrightarrow> (\<exists>z. x = f z \<and> z \<in> set xs)"
  apply (induct xs)
   apply simp
  apply auto
  done

lemma in_set_sort:
  "x \<in> set (sort xs) = (x \<in> set xs)"
  by force

lemma in_set_remdups:
  "x \<in> set (remdups xs) = (x \<in> set xs)"
  by force

lemma in_set_sort_remdups_map_fst:
  "x \<in> set (sort (remdups (map fst (filter (\<lambda>(t, _). t \<le> wm) data)))) \<Longrightarrow> x \<le> wm"
  apply (subst (asm) in_set_sort)
  apply (subst (asm) in_set_remdups)
  apply (simp split: prod.splits)
  apply safe
  apply simp
  done

lemma sorted_tail_gt:
  "xs = t # xs' \<Longrightarrow>
   t' \<in> set xs' \<Longrightarrow> distinct xs \<Longrightarrow> sorted xs \<Longrightarrow> t < t'"
  using strict_sorted_iff strict_sorted_simps(2) by blast

lemma LCons_in_lset: "xs = LCons x xs' \<Longrightarrow> x \<in> lset xs"
  by auto

lemma filter_ge_Max:
  "t \<ge> Max (set (map fst data)) \<Longrightarrow>
   filter (\<lambda> (t', _). t' \<le> t) data =  data"
  by (metis (no_types, lifting) List.finite_set Max.boundedE case_prod_unfold filter.simps(1) filter_True in_set_zip list.map_disc_iff nth_mem set_empty zip_map_fst_snd)

lemma mset_filter_append:
  "inr < (t::_::linorder) \<Longrightarrow>
   mset (filter (\<lambda>x. (case x of (t, _) \<Rightarrow> inr < t) \<and> (case x of (t', _) \<Rightarrow> t' \<le> t)) data @ filter (\<lambda>(t', d'). t' \<le> inr) data) =
   mset (filter (\<lambda>(t', _). t' \<le> t) data)"
  apply (induct data arbitrary: inr t)
   apply simp
  apply (simp split: prod.splits)
  apply safe
    apply force+
  done

lemma mset_filter_append_2:
  "inr < (t::_::linorder) \<Longrightarrow>
   mset (filter (\<lambda>(t', _). t' < inr \<or> t' = inr) data @ filter (\<lambda>x. (case x of (t, _) \<Rightarrow> inr < t) \<and> (case x of (t', _) \<Rightarrow> t' < t \<or> t' = t)) data) =
   mset (filter (\<lambda>(t', _). t' < t \<or> t' = t) data)"
  apply (induct data arbitrary: inr t)
   apply simp
  apply (simp split: prod.splits)
  apply safe
   apply force+
  done

lemma mset_filter_append_filter_mset:
  "filter_mset P (mset M) + filter_mset Q (mset N) = mset (filter P M @ filter Q N)"
  by simp

lemma llength_eSuc_ltl:
  "\<not> lnull xs \<Longrightarrow> llength xs = eSuc (llength (ltl xs))"
  by (simp add: enat_unfold llength_def)

lemma mset_mfilter_simp_cong[simp]:
  "{#x \<in># {#y \<in># A. Q y#}. P x#} =
   {#x \<in># A. P x \<and> Q x#}"
  using multi_count_eq by fastforce


lemma in_lset_finds_tail: "x \<in> lset xs \<Longrightarrow> \<exists> n xs'. ldrop (enat n) xs = LCons x xs'"
  by (metis in_lset_conv_lnth ldrop_enat ldropn_Suc_conv_ldropn)

lemma mset_concat:
  "mset (concat xs) = sum_list (map mset xs)"
  apply (induct xs)
  apply auto
  done

lemma sum_list_sum:
  "distinct xs \<Longrightarrow>
   set xs = A \<Longrightarrow>
   sum_list (map f xs) = sum f A"
  apply (induct xs arbitrary: A)
  apply auto
  done

lemma Sum_sum_sum_sum:
  "card B = card (set ` B) \<Longrightarrow>
   (\<Sum>x\<in> B. sum f (set x)) = sum (sum f) (set ` B)"
  by (metis card_eq_0_iff eq_card_imp_inj_on sum.empty sum.infinite sum.reindex_cong)


lemma Sum_set_sum_list_map_Sum_sum_set:
  "\<forall> x \<in> set xs . distinct x \<Longrightarrow>
   (\<Sum> x\<in>set xs . sum_list (map f x)) = (\<Sum>x\<in>set xs. sum f (set x))"
  by (meson sum.cong sum_list_sum)

lemma sum_change_fun:
  "\<forall> x \<in> A . f x = g x \<Longrightarrow>
   sum f A = sum g A"
  by force

lemma sum_sum_change_fun:
  "\<forall> x \<in> A . sum f x = sum g x \<Longrightarrow>
   sum (sum f) A = sum (sum g) A"
  using sum_change_fun by blast

end