theory Hist
  imports
    "Logic_on_Watermarked_Stream"
    "HOL-Library.Code_Lazy"
begin

definition "multi_incr_hist_op buf1 buf2 =
  compose_op (multi_incr_op buf1 buf2) (map_op multi_incr_coll_list)"

lemma multi_incr_hist_op_soundness:
  "Data t hist \<in> lset (produce (multi_incr_hist_op [] []) lxs) \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   hist = multi_incr_coll_mset lxs t"
  unfolding multi_incr_hist_op_def produce_compose_op_correctness produce_map_op_correctness llist.set_map 
  apply (auto simp add: image_iff split: event.splits)
  subgoal for x 
    apply (cases x)
    apply simp_all
    apply hypsubst_thin
    subgoal for d
      apply (subst (asm) in_lset_conv_lnth)
      apply (elim exE conjE)
      subgoal for n    
        apply (frule produce_multi_incr_op_soundness)
        apply assumption+
        apply simp
        apply (elim exE conjE)
        subgoal for m
          apply hypsubst_thin
          apply (rule mset_multi_incr_coll_list_eq_multi_incr_coll_mset)
          apply simp
          apply safe
          apply simp
          done
        done
      done
    done
  done

lemma multi_incr_hist_op_completeness_aux:
  "(\<exists>i d. enat i < llength lxs \<and> lnth lxs i = Data t d \<and> j = Suc i) \<or> j = 0 \<and> (\<exists>d. (t, d) \<in> set buf1) \<Longrightarrow>
   \<forall>(t', d)\<in>set buf1. lfinite lxs \<or> (\<exists>wm\<ge>t'. Watermark wm \<in> lset lxs) \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   productive lxs \<Longrightarrow>
   \<exists> hist . Data t hist \<in> lset (produce (multi_incr_hist_op buf1 buf2) lxs) \<or> 
   (lfinite lxs \<and> (\<forall>k\<in>{j..<the_enat (llength lxs)}. \<forall>t'\<ge>t. lnth lxs k \<noteq> Watermark t'))"
  apply (frule produce_multi_incr_op_completeness[ of _ _ _ _ _ buf2])
  apply auto[1]
  apply assumption+
  apply (elim exE conjE)
  subgoal for batch
    apply (rule exI[of _ "multi_incr_coll_list t batch"])
    unfolding multi_incr_hist_op_def produce_compose_op_correctness produce_map_op_correctness llist.set_map multi_incr_coll_mset_def 
    apply (auto simp add: image_iff split: event.splits)
    done
  done

lemma multi_incr_hist_op_completeness:
  "\<exists>i d. enat i < llength lxs \<and> lnth lxs i = Data t d \<and> j = Suc i \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   productive lxs \<Longrightarrow>
   \<exists> hist . Data t hist \<in> lset (produce (multi_incr_hist_op [] []) lxs) \<and> multi_incr_coll_mset lxs t = hist \<or> 
   (lfinite lxs \<and> (\<forall>k\<in>{j..<the_enat (llength lxs)}. \<forall>t'\<ge>t. lnth lxs k \<noteq> Watermark t'))"
  using multi_incr_hist_op_completeness_aux[where t=t and lxs=lxs and j=j and WM=WM, of  "[]" "[]"] apply simp
  apply (elim disjE conjE exE)
  apply (rule disjI1)
  apply (frule multi_incr_hist_op_soundness)
  apply assumption+
  apply simp
  apply blast
  done

lemma multi_incr_hist_op_completeness_2:
  "\<exists> d. Data t d \<in> lset lxs \<Longrightarrow>
   \<exists> wm\<ge>t . Watermark wm \<in> lset lxs \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   productive lxs \<Longrightarrow>
   \<exists> hist . Data t hist \<in> lset (produce (multi_incr_hist_op [] []) lxs) \<and> multi_incr_coll_mset lxs t = hist"
  apply (subst (asm) lset_conv_lnth)
  apply auto
  subgoal for d wm n
    using multi_incr_hist_op_completeness[where lxs=lxs and WM=WM and j="Suc n" and t=t] apply -
    apply (drule meta_mp)
    apply metis
    apply (drule meta_mp)
    apply assumption
    apply (drule meta_mp)
    apply assumption
    apply (elim exE conjE disjE)
    apply simp
    apply auto
    apply (rule FalseE)
    apply (metis Watermark_in_lxs_in_sub)
    done
  done

lemma multi_incr_hist_op_completeness_3:
  "\<exists> d. Data t d \<in> lset lxs \<Longrightarrow>
   \<exists> wm\<ge>t . Watermark wm \<in> lset lxs \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   productive lxs \<Longrightarrow>
   Data t (multi_incr_coll_mset lxs t) \<in> lset (produce (multi_incr_hist_op [] []) lxs)"
  apply (meson multi_incr_hist_op_completeness_2)
  done

lemma produce_multi_incr_hist_op_strict_monotone:
  "monotone stream_in WM \<Longrightarrow>
   (\<forall>x\<in>set buf1. \<forall>wm\<in>WM. \<not> fst x \<le> wm) \<Longrightarrow>
   produce (multi_incr_hist_op buf1 buf2) stream_in = stream_out \<Longrightarrow>
   monotone stream_out WM"
  unfolding multi_incr_hist_op_def
  by (metis (no_types, lifting) multi_incr_op_def produce_compose_op_correctness produce_compose_op_sync_op_incr_op_strict_monotone produce_map_op_strict_monotone)

lemma produce_multi_incr_hist_op_productive:
  "productive stream_in \<Longrightarrow>
   monotone stream_in WM \<Longrightarrow>
   produce (multi_incr_hist_op buf1 buf2) stream_in = stream_out \<Longrightarrow>
   productive stream_out"
  unfolding multi_incr_hist_op_def produce_compose_op_correctness
  using produce_map_op_strict_productive produce_multi_incr_op_productive by blast

code_lazy_type llist

declare produce_inner.simps[code]

value "ltaken_Data 10 (produce (multi_incr_hist_op [] []) (LCons (Data 3 2) (LCons (Data 1 2) (LCons (Watermark 3) LNil))::((nat, nat) event) llist))"

primcorec hist_logic where
  "hist_logic H buf = Logic (\<lambda> ev.
     case ev of
       Data (t::_::linorder) d \<Rightarrow> (hist_logic H (buf @ [(t, d)]), [])
     | Watermark wm \<Rightarrow> if \<exists> (t, d) \<in> set buf . t \<le> wm
                  then let out = filter (\<lambda> (t, _) . t \<le> wm) buf ;
                           buf' = filter (\<lambda> (t, _) . t > wm) buf ;
                           ts = rev (remdups (rev (map fst out))) ;
                           Hs = map (\<lambda> t . Data t (H + (mset (map snd (filter (\<lambda> (t', _) . t' \<le> t) out))))) ts in
                           (hist_logic (H + (mset (map snd out))) buf', Hs @ [Watermark wm])
                  else (hist_logic H buf, [])
   )"


lemma finite_produce_Cons[simp]:
  "finite_produce op (x#xs) old = (let (lgc', out) = apply op x in finite_produce lgc' xs (old@out))"
  apply (subst finite_produce_simps)
  apply simp
  done

lemma fst_finite_produce_map_op[simp]:
  "fst (finite_produce (map_op f) xs old) = map_op f"
  apply (induct xs arbitrary: old)
  apply (auto split: event.splits)
  done

term map_event
term get_Data

lemma snd_finite_produce_map_op[simp]:
  "snd (finite_produce (map_op f) xs old) = old @ map (\<lambda> ev . case ev of Watermark wm \<Rightarrow> Watermark wm | Data t d \<Rightarrow> Data t (f t d)) xs"
  apply (induct xs arbitrary: old)
   apply (auto split: event.splits)
  done

lemma filter_chains_linorder[simp]:
  "filter_chains (xs::('a::linorder) list list) = xs"
  unfolding filter_chains_def
  using filter_id_conv not_less_iff_gr_or_eq by auto

(* FIXME: make filter_max_chains use Pow *)
lemma filter_subseqs_Pow[simp]:
  "filter (\<lambda>l. \<forall>l'\<in>set (subseqs xs). \<not> set l \<subset> set l') (subseqs xs) = filter (\<lambda>l. \<forall>l'\<in>Pow (set xs). \<not> set l \<subset> l')  (subseqs xs)"
  by (metis (no_types, lifting) PowD imageI psubset_subset_trans subseqs_powset subseqs_refl)

lemma append_singleton:
  "(xs = [x] \<and> ys = []) \<or> (ys = [x] \<and> xs = []) \<Longrightarrow> xs @ ys = [x]"
  by auto

(* FIXME: move me*)
lemma filter_singleton:
  "distinct xs \<Longrightarrow> 
   P x \<Longrightarrow> 
   x \<in> set xs \<Longrightarrow>
   \<forall> y \<in> (set xs) - {x} . \<not> P y \<Longrightarrow>
   filter P xs = [x]"
  apply (induct xs arbitrary: x)
   apply auto
  done

(* FIXME: move me*)
lemma filter_Pow:
  "distinct xs \<Longrightarrow>
   filter (\<lambda>l. \<forall>l'\<in>Pow (set xs). \<not> set l \<subset> l') (subseqs xs) = [xs]"
  apply (rule filter_singleton)
     apply (auto 0 0 simp add: distinct_List_subseqs)
  apply (metis Pow_top filter_id_conv filter_in_nths filter_is_subset order_le_imp_less_or_eq subseq_conv_nths)
  done

(* FIXME: move me*)
lemma paths_from_list_singleton:
  "distinct xs \<Longrightarrow>
   paths_from_list xs (t::_::linorder) = [(filter (\<lambda> t' . t' < t) xs)]"
  apply (auto simp add: paths_from_list_def filter_max_chains_def Let_def)
  using filter_Pow 
  apply (smt (verit, best) Collect_cong distinct_filter filter_cong set_filter)
  done

term sum

(* FIXME: move me*)
lemma mset_concat_sum:
  "mset (concat (map (\<lambda>t. (filter ((=) t) xs)) (remdups xs))) = sum ((\<lambda>t. mset (filter ((=) t) xs))) (set xs)"
  apply (simp add: mset_concat)
  apply (metis (mono_tags, lifting) comp_apply mset_filter sum.cong sum_code)
  done

lemma mset_concat_fst_sum:
  "mset (concat (map (\<lambda>t. (filter ((=) t \<circ> fst) xs)) (remdups (map fst xs)))) = sum ((\<lambda>t. mset (filter ((=) t \<circ> fst) xs))) (set (map fst xs))"
  apply (simp add: mset_concat)
  apply (metis (mono_tags, lifting) comp_apply filter_cong list.set_map mset_filter sum.cong sum_code)
  done

lemma mset_concat_sum_filter:
  "mset (concat (map (\<lambda>t. (filter ((=) t) xs)) (filter P (remdups xs)))) = sum ((\<lambda>t. mset (filter ((=) t) xs))) (set (filter P xs))"
  apply (simp add: mset_concat)
  by (metis (mono_tags, lifting) comp_apply mset_filter remdups_filter set_filter sum.cong sum_code)


lemma mset_concat_sum_filter_fst:
  "mset (concat (map (\<lambda>t. (filter ((=) t \<circ> fst) xs)) (filter P (remdups (map fst xs))))) = sum ((\<lambda>t. mset (filter ((=) t \<circ> fst) xs))) (set (filter P (map fst xs)))"
    apply (simp add: mset_concat)
  apply (smt (z3) Collect_cong comp_apply filter_cong list.set_map mset_filter remdups_filter set_filter sum.cong sum_code)
  done

lemma mset_concat_sum_filter_fst_snd:
  "mset (concat (map (\<lambda>t. map snd (filter ((=) t \<circ> fst) xs)) (filter P (remdups (map fst xs))))) = sum ((\<lambda>t. mset (map snd (filter ((=) t \<circ> fst) xs)))) (set (filter P (map fst xs)))"
    apply (simp add: mset_concat)
  apply (smt (z3) Collect_cong comp_apply filter_cong list.set_map mset_filter mset_map remdups_filter set_filter sum.cong sum_code)
  done

lemma mset_concat_map_filter_2[simp]:
  "concat (map (\<lambda>t. (filter (\<lambda> t'. t' = t \<and> P t') xs)) ((filter (\<lambda>t'. P t') (remdups xs)))) = concat (map (\<lambda>t. (filter ((=) t) xs)) ((filter (\<lambda>t'. P t') (remdups xs))))"
  by (smt (verit, best) filter_cong map_eq_conv mem_Collect_eq set_filter)

lemma filter_remdups_map:
  "filter P (remdups (map fst xs)) = remdups (map fst (filter (P \<circ> fst ) xs))"
  by (metis filter_map remdups_filter)

(* FIXME: move me*)
lemma mset_concat_map_filter[simp]:
  "mset (concat (map (\<lambda>t. (filter ((=) t) xs)) (remdups xs))) = mset xs"
  apply (induct xs rule: rev_induct)
   apply auto[1]
  apply (drule sym)
  apply (auto simp del: filter.simps filter_append simp add: mset_concat_sum)
  subgoal premises prems for x xs
    apply (smt (verit, ccfv_SIG) Diff_insert_absorb List.finite_set Set.set_insert add.commute add_mset_add_single empty_filter_conv insert_absorb mset.simps(1) mset_filter prems sum.cong sum.insert sum.insert_remove union_mset_add_mset_left)
    done
  done


lemma mset_concat_map_fst_filter[simp]:
  "mset (concat (map (\<lambda>t. (filter ((=) t \<circ> fst) xs)) (remdups (map fst xs)))) = mset xs"
  apply (induct xs rule: rev_induct)
   apply auto[1]
  apply (drule sym)
  apply (subst (asm) mset_concat_fst_sum)
  apply (subst  mset_concat_fst_sum)
  apply (auto simp del: filter.simps filter_append simp add: mset_concat_fst_sum)
  using Diff_insert_absorb List.finite_set Set.set_insert add.commute add_mset_add_single empty_filter_conv insert_absorb mset.simps(1) mset_filter sum.cong sum.insert sum.insert_remove union_mset_add_mset_left
  apply (smt (verit, ccfv_SIG) finite_imageI image_iff)
  done

lemma Sum_if_true:
  "finite A \<Longrightarrow>
   a \<in> A \<Longrightarrow> 
   (\<Sum>t\<in>A. if t = a then G t else F t) = G a + (\<Sum>t\<in>A - {a}. F t)"
  apply (induct A arbitrary: a  rule: finite_induct)
   apply auto
   apply (smt (verit, ccfv_SIG) add.commute sum.cong)
  apply (simp add: ab_semigroup_add_class.add_ac(1) insert_Diff_if)
  using add.left_commute apply blast
  done

lemma Sum_if_false:
  "finite A \<Longrightarrow>
   a \<notin> A \<Longrightarrow> 
   (\<Sum>t\<in>A. if t = a then G t else F t) = (\<Sum>t\<in>A - {a}. F t)"
  apply (induct A arbitrary: a  rule: finite_induct)
   apply auto
  done


lemma Sum_mset_filter_mset:
  "finite A \<Longrightarrow>
   (\<Sum>t\<in>A. {#x \<in># M. t = x#}) = {#t' \<in># M. t' \<in> A#}"
    apply (induct M arbitrary: A rule: multiset_induct)
   apply simp_all
  apply safe
  subgoal for a N A
    apply (subst Sum_if_true)
      apply assumption+
    apply (metis add.commute insert_absorb sum.insert_remove union_mset_add_mset_left)
    done
  subgoal for a N A
    apply (subst Sum_if_false)
      apply assumption+
    apply simp
    done
  done

lemma image_mset_Sum:
  "finite S \<Longrightarrow>
   image_mset g (\<Sum>t\<in>S. f t) = (\<Sum>t\<in>S. image_mset g (f t))"
  apply (induct S rule: finite_induct)
   apply auto
  done


lemma Sum_image_set_snd:
  "(\<Sum>t\<in>fst ` set xs. image_mset snd {#x \<in># mset xs. t = fst x#}) = image_mset snd (\<Sum>t\<in>set xs. filter_mset ((=) t) (mset xs))"
  apply (subst image_mset_Sum)
   apply simp
  apply (induct xs)
   apply (auto simp add: split_beta split: if_splits)
  apply (smt (verit) Diff_insert_absorb List.finite_set Set.set_insert add.commute add_mset_add_single empty_filter_conv finite_imageI image_def image_mset_add_mset image_mset_is_empty_iff insertCI insert_Diff1 mem_Collect_eq mset.simps(1) mset_filter sum.cong sum.insert_remove union_mset_add_mset_left)
  done

lemma Sum_filter_mset_add:
  "finite A \<Longrightarrow>
   a \<in> fst ` A \<Longrightarrow>
   (\<Sum>t\<in>fst ` A. image_mset snd (filter_mset ((=) t \<circ> fst) (add_mset (a, b) M))) =
   add_mset b (\<Sum>t\<in>fst ` A. image_mset snd (filter_mset ((=) t \<circ> fst) M))"
  apply (induct A arbitrary: a b rule: finite_induct)
   apply auto
    apply (smt (verit, best) Diff_insert_absorb Set.set_insert finite_imageI image_mset_add_mset insertCI insert_Diff1 snd_conv sum.cong sum.insert_remove union_mset_add_mset_left)
  apply (smt (z3) Diff_iff Diff_insert_absorb Set.set_insert finite_imageI finite_insert fst_conv image_insert image_mset_add_mset snd_conv sum.cong sum.insert_remove union_mset_add_mset_left)
  done

lemma image_mset_minus:
  "x \<in> set xs \<Longrightarrow>
   image_mset snd {#t' \<in># {#x#}. fst t' < t#} + (image_mset snd {#t' \<in># mset xs. fst t' < t#} - image_mset snd {#t' \<in># {#x#}. fst t' < t#}) =
   image_mset snd {#t' \<in># mset xs. fst t' < t#}"
  apply simp
  done

lemma Sum_set_image_mset[simp]:
 "(\<Sum>t\<in>fst ` {x \<in> set xs. fst x < t}. image_mset snd (filter_mset ((=) t \<circ> fst) (mset xs))) =
  image_mset snd (\<Sum>t\<in>fst ` {x \<in> set xs. fst x < t}. (filter_mset ((=) t \<circ> fst) (mset xs)))"
  by (simp add: image_mset_Sum)


lemma Collect_mset_filter_mset[simp]:
  "{#t' \<in># mset xs. t' \<in>  {x \<in> set xs. P (fst x)}#} = filter_mset (P \<circ> fst) (mset xs)"
  by (metis (mono_tags, lifting) comp_apply count_mset_0_iff filter_mset_cong mem_Collect_eq not_in_iff)

lemma Sum_filter_mset_add_alt:
  "finite A \<Longrightarrow>
   a \<in> fst ` A \<Longrightarrow>
   (\<Sum>t\<in>fst ` A. (filter_mset ((=) t \<circ> fst) (add_mset (a, b) M))) =
   add_mset (a, b) (\<Sum>t\<in>fst ` A. (filter_mset ((=) t \<circ> fst) M))"
  apply (induct A arbitrary: a b rule: finite_induct)
   apply auto
  apply (smt (verit, best) Diff_insert_absorb finite_imageI finite_insert fst_conv insertCI insert_absorb sum.cong sum.insert_remove union_mset_add_mset_left)
  apply (smt (z3) Diff_iff Diff_insert_absorb Set.set_insert finite_imageI finite_insert fst_conv image_eqI insert_absorb multi_self_add_other_not_self sum.cong sum.insert_remove union_mset_add_mset_left)
  done

lemma Collect_add_mset:
  "{#x \<in># add_mset (a, b) M. P (fst x)#} = {#x \<in># M. P (fst x)#} + {#x \<in># {#(a, b)#}. P (fst x)#}"
  apply simp
  done

lemma Sum_filter_mset_mset:
  "(\<Sum>t\<in>{x \<in> set xs. P x}. filter_mset ((=) t) (mset xs)) = {#x \<in># mset xs. P x#}"
  apply (subst Sum_mset_filter_mset)
   apply simp
  apply (metis (no_types, lifting) filter_mset_cong mem_Collect_eq set_mset_mset)
  done

lemma filter_mset_image_mset:
  "filter_mset P (image_mset f xs) = image_mset f (filter_mset (P \<circ> f) xs)"
  by (metis comp_apply filter_mset_cong image_mset_filter_mset_swap)

lemma mset_Collect_filter_mset:
  "{#x \<in># M. P (f x)#} = filter_mset (P \<circ> f) M"
  by (metis comp_apply)

lemma Sum_mset_mset_image:
  "(\<Sum>t\<in>f ` {x \<in> set_mset M. P (f x)}. {#t' \<in># M. t = f t'#}) = {#x \<in># M. P (f x)#}"
  by (auto simp: multiset_eq_iff count_sum)

lemma Sum_mset_mset_fst:
  "(\<Sum>t\<in>fst ` {x \<in> set xs. P (fst x)}. filter_mset ((=) t \<circ> fst) (mset xs)) = {#x \<in># mset xs. P (fst x)#}"
  by (auto simp: multiset_eq_iff count_sum image_iff)

lemma multi_incr_coll_list_linorder[simp]:
  "multi_incr_coll_list (t::_::linorder) xs = mset (map snd (filter (\<lambda> (t', _) . t' \<le> t) xs))"
  unfolding multi_incr_coll_list_def
  apply (subst paths_from_list_singleton)
   apply simp
  apply simp
  unfolding coll_list_def
  apply (auto simp add: order.order_iff_strict)
  apply (subgoal_tac "{#x \<in># mset xs. case x of (t', uu_) \<Rightarrow> t' < t \<or> t' = t#} = {#x \<in># mset xs. case x of (t', uu_) \<Rightarrow> t' < t#} + {#x \<in># mset xs. case x of (t', uu_) \<Rightarrow> t' = t#}")
   defer
  subgoal
    apply (induct xs)
     apply auto
    done
  apply clarsimp
  subgoal premises 
    apply (rule arg_cong2[where f="(+)"])
     defer
     apply (metis (mono_tags, lifting) case_prod_unfold)
    apply (subst mset_concat_sum_filter_fst_snd)
    apply (subst filter_map)
    apply (subst set_map)
    apply (subst mset_map)
    apply (subst mset_filter)
    apply (subgoal_tac "image_mset snd {#(t', _) \<in># mset xs. t' < t#} = image_mset snd {#t' \<in># mset xs. fst t' < t#}")
     defer
     apply (metis (mono_tags, lifting) case_prod_unfold )
    apply (simp only: )
    subgoal premises
      apply simp
      apply (subst Sum_mset_mset_fst[symmetric])
      apply simp
      done
    done
  done

abbreviation OP_EQ where
  "OP_EQ ev p WM op1 op2 \<equiv> (case ev of Data t d \<Rightarrow> (\<forall>wm\<in>WM. \<not> t \<le> wm) \<longrightarrow> rel_prod (p WM) (=) (apply op1 ev) (apply op2 ev)
              | Watermark wm \<Rightarrow> (\<forall>wm'\<in>WM. \<not> wm \<le> wm') \<longrightarrow> rel_prod (p (insert wm WM)) (=) (apply op1 ev) (apply op2 ev))"

definition WM_EQ where
  "WM_EQ = (\<lambda>p WM op1 op2. 
        (\<forall>ev. OP_EQ ev p WM op1 op2))"

definition wm_eq where
  "wm_eq = gfp WM_EQ"

term rel_prod

lemma wm_eq_mono:
  "mono WM_EQ"
  apply (auto simp: WM_EQ_def rel_prod_sel le_fun_def mono_def split: event.splits)
  done

thm wm_eq_mono[unfolded mono_def le_fun_def le_bool_def, THEN spec2, THEN mp]

lemmas wm_eq_coinduct = coinduct[OF wm_eq_mono, folded wm_eq_def, unfolded WM_EQ_def le_fun_def le_bool_def, rule_format, rotated, of R WM op1 op2 for R WM op1 op2]

thm wm_eq_coinduct[no_vars]
term rel_prod
lemma hist_logic_eq_multi_incr_hist_op:
  "\<forall> t \<in> fst ` set buf2 . \<exists> wm \<in> WM . t \<le> wm \<Longrightarrow>
   \<forall> t \<in> fst ` set buf1 . \<forall> wm \<in> WM . t > wm \<Longrightarrow>
   wm_eq WM (hist_logic (mset (map snd buf2)) buf1) (multi_incr_hist_op buf1 buf2)"
    unfolding multi_incr_hist_op_def multi_incr_op_def
  apply (coinduction arbitrary: WM buf1 buf2 rule: wm_eq_coinduct)
  apply (auto simp: comp_def rel_fun_def finite_produce_append not_le rev_map split: list.splits event.splits)
  subgoal for wm buf1 buf2 t d
    apply (rule exI)+
    apply (rule conjI[rotated])
     apply (rule conjI)
    apply (rule refl)
      apply (auto simp: le_max_iff_disj)
    done
  subgoal for wm buf1 buf2 t d
    apply (rule exI)+
    apply (rule conjI[rotated])
     apply (rule conjI)
    apply (rule refl)
      apply (auto simp: le_max_iff_disj)
    done
  subgoal for wm buf1 buf2 wm' t' d' t d
        apply (rule arg_cong2[where f="(+)"])
         apply (rule arg_cong2[where f="image_mset"])
      apply (simp_all add: conj_commute)
     apply (rule multiset_eqI)
    apply auto
    apply (metis fst_conv image_eqI less_le_not_le order_trans)
    done
  subgoal for wm buf1 buf2 t 
    apply (rule exI)+
    apply (rule conjI[rotated])
     apply (rule conjI)
    apply (rule refl)
     apply (auto simp: le_max_iff_disj)
    done
  done

lemmas wm_eq_cases = gfp_unfold[OF wm_eq_mono, folded wm_eq_def, unfolded WM_EQ_def, THEN fun_cong, THEN fun_cong, THEN fun_cong, THEN iffD1, elim_format]
lemmas wm_eq_intros = gfp_unfold[OF wm_eq_mono, folded wm_eq_def, unfolded WM_EQ_def, THEN fun_cong, THEN fun_cong, THEN fun_cong, THEN iffD2]

lemma wm_eq_sym:
  "wm_eq WM op1 op2 \<Longrightarrow> wm_eq WM op2 op1"
  apply (coinduction arbitrary: WM op1 op2 rule: wm_eq_coinduct) 
  apply (auto simp add: rel_prod_sel split: event.splits elim!: wm_eq_cases)
    apply metis+
  done

lemma wm_eq_refl[simp]:
  "wm_eq WM op op"
  apply (coinduction arbitrary: WM op rule: wm_eq_coinduct) 
  apply (auto simp add: rel_prod_sel split: event.splits)
  done

lemma produce_inner_wm_eq:
  "produce_inner (op2, lxs) = Some (op', x, xs, lxs') \<Longrightarrow> wm_eq WM op1 op2 \<Longrightarrow>
   monotone lxs WM \<Longrightarrow> produce_inner (op1, lxs) = None \<Longrightarrow> False"
  apply (induct "(op2, lxs)" "(op', x, xs, lxs')" arbitrary: lxs x xs lxs' op1 op2 WM rule: produce_inner_alt[consumes 1])
  subgoal for op h lxs' lgc' x xs lxs'a op1 WM
   apply (subst (asm) (2) produce_inner.simps)
    apply (erule wm_eq_cases)
    apply (drule spec[of _ h])
    apply (auto split: if_splits event.splits list.splits prod.splits elim: LConsData LConsWatermark)
    done
  subgoal for op h x xs lxs' op1 WM
    apply (subst (asm) produce_inner.simps)
   apply (erule wm_eq_cases)
    apply (drule spec[of _ h])
    apply (auto split: if_splits event.splits list.splits prod.splits elim: LConsData LConsWatermark)
    done
  done

lemma not_wm_eq_not_eq:
  "\<not> wm_eq WM op1 op2 \<Longrightarrow>
   op1 \<noteq> op2"
  using wm_eq_refl by blast

lemma produce_inner_wm_eq_Some_Some:
  "produce_inner (op1, lxs) = Some (op1', x, xs, lxs') \<Longrightarrow>
   wm_eq WM op1 op2 \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   produce_inner (op2, lxs) = Some (op2', y, ys, lys') \<Longrightarrow>
   lxs' = lys' \<and> x = y \<and> xs = ys"
  apply (induct "(op1, lxs)" "(op1', x, xs, lxs')" arbitrary: lxs x xs lxs' op1 op2 op1' op2' y ys lys' WM rule: produce_inner_alt[consumes 1])
  subgoal for op h lxs' lgc' x xs lxs'a op1' op2 op2' y ys lys' WM'
    apply (subst (asm) (2) produce_inner.simps)
    apply (erule wm_eq_cases)
    apply (drule spec[of _ h])
    apply (auto split: if_splits event.splits list.splits prod.splits elim: LConsData LConsWatermark)
    done
  subgoal for op h x xs lxs' lgc' op2 op2' y ys lys' WM
    apply (subst (asm) (1) produce_inner.simps)
    apply (erule wm_eq_cases)
    apply (drule spec[of _ h])
    apply (auto split: if_splits event.splits list.splits prod.splits elim: LConsData LConsWatermark)
    done
  done

(* FIXME: Move me *)
lemma produce_inner_ldropn_inversion:
  "produce_inner (op, lxs) = Some (op', x, xs', lxs') \<Longrightarrow> \<exists> n . lxs' = ldropn n lxs \<and> n > 0 \<and> lxs \<noteq> LNil"
  subgoal premises prems
    using prems apply -
    apply (induct "(op, lxs)" "(op', x, xs', lxs')" arbitrary: lxs op op' rule: produce_inner_alt)
    using prems apply simp
    subgoal for op h lxs'a lgc' op'
      apply (subst (asm) (2) produce_inner.simps)
      apply (simp split: llist.splits event.splits)
      apply (metis ldropn_Suc_LCons zero_less_Suc)
      done
    subgoal for op h lgc
      apply (subst (asm) produce_inner.simps)
      apply (force split: llist.splits event.splits)
      done
    done
  done

lemma produce_inner_monotone_inversion:
  "produce_inner (op, lxs) = Some (op', x, xs', lxs') \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   \<exists> n . lxs' = ldropn n lxs \<and> n > 0 \<and> monotone lxs' (wms (list_of (ltake n lxs)) \<union> WM)"
  subgoal premises prems
    using prems apply -
    apply (induct "(op, lxs)" "(op', x, xs', lxs')" arbitrary: lxs op op' WM lxs' rule: produce_inner_alt)
    using prems apply simp
    subgoal for op h lxs' op'' op' lxs'' WM
      apply (cases h)
      subgoal for t d
      apply (subst (asm) (2) produce_inner.simps)
        apply (simp split: llist.splits event.splits)
        apply hypsubst_thin
        apply (drule meta_spec[of _ WM])
        apply (drule meta_mp)
        using strict_monotone_drop_head apply blast
        apply force
        done
      subgoal for wm
      apply (subst (asm) (2) produce_inner.simps)
        apply (simp split: llist.splits event.splits)
        apply hypsubst_thin
        apply (drule meta_spec[of _ "insert wm WM"])
        apply (drule meta_mp)
        using strict_monotone_LCons_Watermark_insert apply blast
        apply force
        done
      done
    subgoal for op h lxs' lgc' WM
      apply (cases h)
      subgoal for t d
      apply (subst (asm)  produce_inner.simps)
        apply (simp split: llist.splits event.splits)
        apply (rule exI[of _ 1])
        apply auto
        using strict_monotone_drop_head zero_enat_def apply auto
        done
      subgoal for wm
      apply (subst (asm)  produce_inner.simps)
        apply (simp split: llist.splits event.splits)
        apply (rule exI[of _ 1])
        apply auto
        using strict_monotone_drop_head zero_enat_def 
        apply (simp add: strict_monotone_LCons_Watermark_insert)
        done
      done
    done
  done


lemma produce_inner_Some_wm_eq_ldropn:
  "produce_inner (op1, lxs) = Some (op1', x, xs, lxs') \<Longrightarrow>
   wm_eq WM op1 op2 \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   produce_inner (op2, lxs) = Some (op2', x, xs, lxs') \<Longrightarrow>
   \<exists> n . wm_eq (wms (list_of (ltake n lxs)) \<union> WM) op1' op2' \<and> ldropn n lxs = lxs' \<and> n > 0 \<and> monotone lxs' (wms (list_of (ltake n lxs)) \<union> WM)"
  apply (induct "(op1, lxs)" "(op1', x, xs, lxs')" arbitrary: lxs x xs  op1 op2 op1' op2' lxs' WM rule: produce_inner_alt[consumes 1])
  subgoal for op h lxs' lgc' x xs op1' lxs'a op2 op2' WM
    apply (subst (asm) (2) produce_inner.simps)
    apply (erule wm_eq_cases)
    apply (drule spec[of _ h])
    apply (auto split: if_splits event.splits list.splits prod.splits elim: LConsData LConsWatermark)
    subgoal for t d op'
      apply (drule meta_spec[of _ op'])
      apply (drule meta_spec[of _ op2'])
      apply (drule meta_spec[of _ WM])
      apply (drule meta_mp)
       apply assumption
      apply (drule meta_mp)
      using strict_monotone_drop_head apply blast
      apply (drule meta_mp)
       apply assumption
      apply auto
      apply hypsubst_thin
      subgoal for n
        apply (rule exI[of _ "Suc n"])
        apply simp
        done
      done
    subgoal for wm op'
    apply (drule meta_spec[of _ op'])
      apply (drule meta_spec[of _ op2'])
      apply (drule meta_spec[of _ "insert wm WM"])
      apply (drule meta_mp)
       apply assumption
      apply (drule meta_mp)
      using strict_monotone_LCons_Watermark_insert apply blast
      apply (drule meta_mp)
       apply assumption
      apply auto
      apply hypsubst_thin
      subgoal for n
        apply (rule exI[of _ "Suc n"])
        apply simp
        done
      done
    done
  subgoal for op h x xs lxs' lgc' op2 op2' WM
    apply (subst (asm) produce_inner.simps)
    apply (erule wm_eq_cases)
    apply (drule spec[of _ h])
    apply (auto split: if_splits event.splits list.splits prod.splits elim: LConsData LConsWatermark)
    using ldropn_0 ldropn_Suc_LCons list_of_llist_of ltake_eSuc_LCons ltake_eq_LNil_iff shift_LNil singleton_lshift sup_bot.right_neutral sup_commute wms.simps(1) wms.simps(3) zero_enat_def
    apply (metis eSuc_enat strict_monotone_drop_head zero_less_Suc)
    using  One_nat_def Suc_ile_eq Un_insert_left enat_ord_code(4) iless_Suc_eq
    ldropn_0 ldropn_Suc_conv_ldropn lfinite_ltake linorder_not_le list_of_LCons list_of_LNil llength_LCons
   llist.inject ltake.ctr(1) ltake_eSuc_LCons nless_le not_eSuc_ilei0 one_eSuc one_enat_def sup_bot.right_neutral sup_commute wms.simps(1) wms.simps(2)
    apply (smt (z3) One_nat_def Un_insert_left enat_ord_code(4) eq_LConsD ldropn_0 ldropn_Suc_conv_ldropn less_Suc_eq lfinite_ltake linorder_not_le list_of_LCons list_of_LNil llength_LCons ltake_eSuc_LCons ltake_eq_LNil_iff not_eSuc_ilei0 one_eSuc one_enat_def strict_monotone_LCons_Watermark_insert sup_bot.right_neutral sup_commute wms.simps(1) wms.simps(2) zero_enat_def)
    done
  done

lemma wm_eq_soundness:
  "wm_eq WM op1 op2 \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   produce op1 lxs = produce op2 lxs"
  apply (coinduction arbitrary: op1 op2 lxs WM rule: llist.coinduct_upto)
  apply (intro allI impI conjI)
  subgoal for op1 op2 lxs WM
    apply (subst (1 2) produce.code)
    apply (fastforce dest: produce_inner_wm_eq produce_inner_wm_eq[OF _ wm_eq_sym] split: option.splits)
    done
  subgoal for op1 op2 lxs WM
    apply (subst (1 2) produce.code)
    apply (auto dest: produce_inner_wm_eq_Some_Some produce_inner_wm_eq produce_inner_wm_eq[OF _ wm_eq_sym] split: option.splits)
    done
  subgoal for op1 op2 lxs WM
    apply (subst (3 4) produce.code)
    apply (auto  dest: produce_inner_wm_eq produce_inner_wm_eq[OF _ wm_eq_sym] simp add: llist.cong_refl split: option.splits)
    apply (rule llist.cong_lshift)
    subgoal 
      apply (auto dest: produce_inner_wm_eq_Some_Some produce_inner_wm_eq produce_inner_wm_eq[OF _ wm_eq_sym] split: option.splits)
      done
    subgoal for op1' x xs lxs' op2' y ys lys
    apply (rule llist.cong_base)
       apply (frule produce_inner_wm_eq_Some_Some)
          apply assumption+
       apply (elim conjE)
       apply hypsubst_thin      
      apply (frule produce_inner_Some_wm_eq_ldropn)
       apply assumption+
       apply (elim conjE exE)
      subgoal for n
        apply (rule exI conjI refl)+
        defer
         apply assumption
        apply hypsubst_thin
        apply simp
        done
      done
    done
  done

end