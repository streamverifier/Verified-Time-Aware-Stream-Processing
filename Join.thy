theory Join
  imports
    "Sum_Order"
    "Logic_on_Watermarked_Stream"
begin

definition join_list where
  "join_list join st xs = 
  (let t = (case st of Inr t \<Rightarrow> t | Inl t \<Rightarrow> t) in
   let lefts = List.map_filter (\<lambda> (v, d). case v of Inr _ \<Rightarrow> None | Inl t' \<Rightarrow> if t = t' then Some d else None) xs in
   let rights = List.map_filter (\<lambda> (v, d). case v of Inl _ \<Rightarrow> None | Inr t' \<Rightarrow> if t = t' then Some d else None) xs in
   concat (map (\<lambda> d1 . List.map_filter (\<lambda> d2 . join d1 d2) rights) lefts))"

lemma map_filter_Nil_conv:
  "List.map_filter P xs \<noteq> [] = (\<exists> x \<in> set xs . P x \<noteq> None)"
  apply (induct xs)
  apply (simp add: List.map_filter_simps)
  apply (auto simp add: List.map_filter_simps split: option.splits)
  done

lemma concat_neq_Nil_conv:
  "concat xs \<noteq> [] = (\<exists> ys \<in> set xs . ys \<noteq> [])"
  using concat_eq_Nil_conv by blast

lemma concat_map_map_filter_neq_Nil_conv:
  "concat (map (\<lambda> d1 . List.map_filter (\<lambda> d2 . join d1 d2) rights) lefts) \<noteq> [] =
   (\<exists> right \<in> set rights . \<exists> left \<in> set lefts . join left right \<noteq> None)"
  apply (induct rights arbitrary: lefts)
  apply (simp add: List.map_filter_simps)
  apply (auto simp add: List.map_filter_simps split: option.splits)
   apply (metis option.distinct(1))
  apply blast
  done  

lemma in_set_map_filter_D:
  "x \<in> set (List.map_filter P xs)  \<Longrightarrow> \<exists> y \<in> set xs . P y = Some x"
  by (smt (verit, ccfv_SIG) filter_set map_eq_set_D map_filter_def member_filter o_apply option.collapse)

lemma join_list_neq_Nil_D:
  "join_list join st xs \<noteq> [] \<Longrightarrow>
   (case st of Inr t \<Rightarrow> t | Inl t \<Rightarrow> t) = t \<Longrightarrow>
   \<exists> d1 d2. ((Inr t), d2) \<in> set xs \<and> ((Inl t), d1) \<in> set xs \<and> join d1 d2 \<noteq> None"
  unfolding join_list_def Let_def 
  apply (simp add: concat_map_map_filter_neq_Nil_conv map_filter_Nil_conv)
  apply (elim bexE conjE)
  apply (auto split: if_splits sum.splits option.splits)
  subgoal for d1 d2 y'
    apply (rule exI[of _ d1])
    apply (rule exI[of _ d2])
    apply auto
    subgoal
      apply (drule in_set_map_filter_D)
      apply (auto split: prod.splits sum.splits if_splits)
      apply (smt (verit, best) in_set_map_filter_D is_none_code(2) is_none_simps(1) option.sel prod.case_eq_if prod.collapse sum.case_eq_if sum.split_sels(2))
      done
    subgoal
      apply (drule in_set_map_filter_D)
      apply (auto split: prod.splits sum.splits if_splits)
      apply (metis old.sum.exhaust)
      done
    done
  subgoal for d1 d2 y'
    apply (rule exI[of _ d1])
    apply (rule exI[of _ d2])
    apply auto
    subgoal
      apply (drule in_set_map_filter_D)
      apply (auto split: prod.splits sum.splits if_splits)
      apply (smt (verit, best) in_set_map_filter_D is_none_code(2) is_none_simps(1) option.sel prod.case_eq_if prod.collapse sum.case_eq_if sum.split_sels(2))
      done
    subgoal
      apply (drule in_set_map_filter_D)
      apply (auto split: prod.splits sum.splits if_splits)
      apply (metis old.sum.exhaust)
      done
    done
  done

lemma in_join_list_D:
  "d \<in> set (join_list join st xs) \<Longrightarrow>
   (case st of Inr t \<Rightarrow> t | Inl t \<Rightarrow> t) = t \<Longrightarrow>
   \<exists> d1 d2. ((Inr t), d2) \<in> set xs \<and> ((Inl t), d1) \<in> set xs \<and> join d1 d2 = Some d"
  unfolding join_list_def Let_def 
  apply (simp add: concat_map_map_filter_neq_Nil_conv map_filter_Nil_conv)
  apply (elim bexE conjE)
  apply (auto split: if_splits sum.splits option.splits)
  subgoal for z
      apply (smt (verit) in_set_map_filter_D is_none_code(2) is_none_simps(1) old.sum.exhaust option.sel prod.case_eq_if prod.collapse sum.case_eq_if sum.split_sels(2))
    done
  subgoal for x
      apply (smt (verit) in_set_map_filter_D is_none_code(2) is_none_simps(1) old.sum.exhaust option.sel prod.case_eq_if prod.collapse sum.case_eq_if sum.split_sels(2))
    done
  done

lemma in_join_list_Inr:
  "(Inr t, d2) \<in> set batch \<Longrightarrow>
   (Inl t, d1) \<in> set batch \<Longrightarrow>
   join d1 d2 = Some x \<Longrightarrow>
   x \<in> set (join_list join (Inr t) batch)"
  apply (induct batch arbitrary: x d1 d2 t)
   apply simp
  subgoal for a batch x d1 d2 t
    apply (auto simp add: concat_map_map_filter_neq_Nil_conv map_filter_Nil_conv split: if_splits sum.splits option.splits)
    subgoal
      unfolding join_list_def Let_def 
      apply (auto simp add: List.map_filter_simps(1)  concat_map_map_filter_neq_Nil_conv map_filter_Nil_conv split: if_splits sum.splits option.splits)
      apply (rule bexI[of _ d1])
       apply auto
      unfolding List.map_filter_def
      apply (auto simp add: concat_map_map_filter_neq_Nil_conv map_filter_Nil_conv split: event.splits if_splits sum.splits option.splits)
      using image_iff apply fastforce
      done
   subgoal
      unfolding join_list_def Let_def List.map_filter_def
      apply (auto simp add: List.map_filter_simps(1)  concat_map_map_filter_neq_Nil_conv map_filter_Nil_conv split: if_splits sum.splits option.splits)
      apply (smt (verit, ccfv_threshold) case_prod_conv image_eqI mem_Collect_eq old.sum.simps(6) option.sel)
      done
  subgoal
      unfolding join_list_def Let_def List.map_filter_def
      apply (auto split: if_splits sum.splits option.splits event.splits)
      apply (cases a)
      apply (auto split: if_splits sum.splits option.splits event.splits)
      apply (cases a)
      apply (auto split: if_splits sum.splits option.splits event.splits)
      apply (rule exI[of _ "Inl t"])
      apply (auto split: if_splits sum.splits option.splits event.splits)
      apply (rule exI[of _ d1])
      apply (auto split: if_splits sum.splits option.splits event.splits)
      apply (smt (verit, del_insts) Pair_inject image_iff mem_Collect_eq old.sum.simps(6) option.sel prod.case_eq_if prod.collapse)
      done
    done
  done

lemma in_join_list_Inl:
  "(Inr t, d2) \<in> set batch \<Longrightarrow>
   (Inl t, d1) \<in> set batch \<Longrightarrow>
   join d1 d2 = Some x \<Longrightarrow>
   x \<in> set (join_list join (Inl t) batch)"
  apply (induct batch arbitrary: x d1 d2 t)
   apply simp
  subgoal for a batch x d1 d2 t
    apply (auto simp add: concat_map_map_filter_neq_Nil_conv map_filter_Nil_conv split: if_splits sum.splits option.splits)
    subgoal
      unfolding join_list_def Let_def 
      apply (auto simp add: List.map_filter_simps(1)  concat_map_map_filter_neq_Nil_conv map_filter_Nil_conv split: if_splits sum.splits option.splits)
      apply (rule bexI[of _ d1])
       apply auto
      unfolding List.map_filter_def
      apply (auto simp add: concat_map_map_filter_neq_Nil_conv map_filter_Nil_conv split: event.splits if_splits sum.splits option.splits)
      using image_iff apply fastforce
      done
   subgoal
      unfolding join_list_def Let_def List.map_filter_def
      apply (auto simp add: List.map_filter_simps(1)  concat_map_map_filter_neq_Nil_conv map_filter_Nil_conv split: if_splits sum.splits option.splits)
      apply (smt (verit, ccfv_threshold) case_prod_conv image_eqI mem_Collect_eq old.sum.simps(6) option.sel)
      done
  subgoal
      unfolding join_list_def Let_def List.map_filter_def
      apply (auto split: if_splits sum.splits option.splits event.splits)
      apply (cases a)
      apply (auto split: if_splits sum.splits option.splits event.splits)
      apply (cases a)
      apply (auto split: if_splits sum.splits option.splits event.splits)
      apply (rule exI[of _ "Inl t"])
      apply (auto split: if_splits sum.splits option.splits event.splits)
      apply (rule exI[of _ d1])
      apply (auto split: if_splits sum.splits option.splits event.splits)
      apply (smt (verit, del_insts) Pair_inject image_iff mem_Collect_eq old.sum.simps(6) option.sel prod.case_eq_if prod.collapse)
      done
    done
  done

lemma mset_concat_remove1:
  "x \<in># mset xs \<Longrightarrow>
  mset (f x) + mset (concat (map f (remove1 x xs))) = mset (concat (map f xs))"
  apply (induct xs)
   apply simp
  apply auto
  done

(* FIXME: move me*)
lemma mset_mset_concat_map:
  "mset xs = mset ys \<Longrightarrow>
  \<forall> x \<in> set xs . mset (f x) = mset (g x) \<Longrightarrow>
   mset (concat (map f xs)) = mset (concat (map g ys))"
  apply (induct xs arbitrary: ys f g)
   apply simp
  subgoal premises prems for a xs ys f g
    using prems(2-) apply auto
    apply (subst prems(1)[of "remove1 a ys"])
      apply (metis add_mset_remove_trivial mset_remove1)
     apply fast
    apply (metis mset_concat_remove1 union_single_eq_member)
    done
  done   

lemma mset_concat_map_map_filter:
  "mset rights1 = mset rights2 \<Longrightarrow>
   mset lefts1 = mset lefts2 \<Longrightarrow>
   mset (concat (map (\<lambda> d1 . List.map_filter (\<lambda> d2 . join d1 d2) rights1) lefts1)) = mset (concat (map (\<lambda> d1 . List.map_filter (\<lambda> d2 . join d1 d2) rights2) lefts2))"
  by (simp add: map_filter_def mset_mset_concat_map)      

lemma image_mset_the_image_mset_Inl:
  "image_mset the
     {#case v of Inl t' \<Rightarrow> if (case Inl t'' of Inl t \<Rightarrow> t | Inr t \<Rightarrow> t) = t' then Some d else None | Inr x \<Rightarrow> Map.empty x. (v,
     d) \<in># {#x \<in># mset xs.
             \<exists>y. (case fst x of Inl t' \<Rightarrow> if (case Inl t'' of Inl t \<Rightarrow> t | Inr t \<Rightarrow> t) = t' then Some (snd x) else None | Inr x \<Rightarrow> Map.empty x) = Some y#}#} =
    image_mset snd {#x \<in># mset xs. Inl t'' = fst x#}"
  apply (induct xs arbitrary: t'')
   apply simp
  apply (auto split: if_splits sum.splits)
  done

lemma image_mset_the_image_mset_Inr:
  "image_mset the
     {#case v of Inl x \<Rightarrow> Map.empty x | Inr t' \<Rightarrow> if (case Inl t'' of Inl t \<Rightarrow> t | Inr t \<Rightarrow> t) = t' then Some d else None. (v,
     d) \<in># {#x \<in># mset xs. \<exists>y. (case fst x of Inl x \<Rightarrow> Map.empty x | Inr t' \<Rightarrow> if (case Inl t'' of Inl t \<Rightarrow> t | Inr t \<Rightarrow> t) = t' then Some (snd x) else None) = Some y#}#} =
    image_mset snd {#x \<in># mset xs. Inr t'' = fst x#}"
  apply (induct xs arbitrary: t'')
   apply simp
  apply (auto split: if_splits sum.splits)
  done

lemma aux2:
  "(t, d) \<in> set (concat (map snd (ltaken_Data n (produce (sync_op buf) lxs)))) \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   productive lxs \<Longrightarrow>
   \<exists> batch wm . (wm, batch) \<in> set (ltaken_Data n (produce (sync_op buf) lxs)) \<and> t \<le> wm \<and> (t, d) \<in> set batch"
  apply (cases n)
   apply simp
  subgoal for n
  apply simp
  apply (elim bexE)
  subgoal for wm_batch
    apply (cases wm_batch)
    subgoal for wm batch
      apply simp
      apply (metis fst_conv image_eqI ltaken_Data_produce_sync_op_in_batch_LE)
      done
    done
  done
  done

definition "join_op buf1 buf2 buf3 join =
  compose_op (compose_op (multi_incr_op buf1 buf2) (compose_op (map_op (join_list join)) flatten_op)) (union_op buf3)"

(* FIXME: move me *)
lemma in_lset_lconcat_LNil_Nil: "xs \<in> lset xss \<Longrightarrow> lconcat xss = LNil \<Longrightarrow> xs = []"
  apply (induct xss arbitrary: rule: lset_induct)
   apply (subst (asm) lconcat_code)
   apply auto
   apply (metis LNil_eq_shift_iff)
  apply (subst (asm) lconcat_code)
  apply auto
  apply (metis LNil_eq_shift_iff)
  done

lemma all_in_lset_lconcat_LNil_Nil: "lconcat xss = LNil \<Longrightarrow> \<forall> xs \<in> lset xss. xs = []"
  using in_lset_lconcat_LNil_Nil apply auto
  done

lemma lconcat_not_all_Nil:
  "x \<in> lset (lconcat xss) \<Longrightarrow> \<not> (\<forall>xs\<in>lset xss. xs = [])"
  using lconcat_all_Nil by fastforce

lemma lconcat_eq_LNil[simp]: "lconcat xss = LNil \<longleftrightarrow> (\<forall>xs\<in>lset xss. xs = [])"
  using in_lset_lconcat_LNil_Nil lconcat_all_Nil by blast

lemma lconcat_LCons_ex:
  "lconcat lxs = LCons x lxs' \<Longrightarrow> \<exists>xa\<in>lset lxs. x \<in> set xa"
  apply (induct lxs rule: lconcat.corec.inner_induct)
  subgoal for xss
    apply (cases xss)
       apply (simp add: lconcat.code)
    subgoal for x xss'
      apply hypsubst_thin
      apply simp
      apply (subst (asm) (2) lconcat_code)
      apply (auto split: llist.splits)
      apply (metis lconcat_all_Nil llist.distinct(1) lshift.simps(1) shift_in_list)
      done
    done
  done

lemma abomination:
  "lconcat lxs = LCons x xs \<Longrightarrow>
   lconcat (LCons (tl (lhd (ldropWhile (\<lambda>xs. xs = []) lxs))) (ltl (ldropWhile (\<lambda>xs. xs = []) lxs))) = xs"
  apply (induct lxs arbitrary: x rule: lconcat.corec.inner_induct)
  subgoal for xss
    apply (cases xss)
     apply (simp add: lconcat.code)
    subgoal for x xss'
      apply hypsubst_thin
      apply simp
      apply (subst (asm) (3) lconcat_code)
      apply (auto split: llist.splits)
      apply (metis lconcat_all_Nil llist.distinct(1))
      apply (metis lconcat_code list.collapse llist.case(2) shift_LCons_Cons)
      done
    done
  done

lemma lconcat_inclusion:
  "x \<in> lset lys \<Longrightarrow> lys = lconcat lxs \<Longrightarrow> \<exists>xa\<in>lset lxs. x \<in> set xa"
  apply (induct lys arbitrary: lxs rule: lset_induct)
  using lconcat_LCons_ex apply metis
  subgoal for x' xs lxs
  apply (drule sym)
  apply (drule meta_spec[of _ "LCons (tl (lhd (ldropWhile (\<lambda> xs . xs = []) lxs))) (ltl (ldropWhile (\<lambda> xs . xs = []) lxs))"])
    apply (frule lconcat_LCons_ex)
    using abomination 
    apply (smt (verit, best) in_lset_ldropWhileD in_lset_ltlD lconcat_all_Nil lhd_LCons lhd_ldropWhile_in_lset list.sel(2) list.set_sel(2) llist.distinct(1) lset_cases ltl_simps(2))
    done
  done

lemma inclusion_lconcat:
  "xs \<in> lset lxs \<Longrightarrow> x \<in> set xs \<Longrightarrow> x \<in> lset (lconcat lxs)"
  apply (induct lxs arbitrary: rule: lset_induct)
  apply (auto simp add: lconcat_code)
  done

lemma lset_lconcat:
  "lset (lconcat xss) = (\<Union>xs\<in>lset xss. set xs)"
  apply safe
  subgoal for x
    apply (induct "(Logic_on_Watermarked_Stream.lconcat xss)" arbitrary: rule: lset_induct)
     apply (metis UN_I lconcat_LCons_ex)
    using lconcat_inclusion 
    apply (metis UN_iff in_lset_ltlD ltl_simps(2))
    done
  subgoal for x xs
    using inclusion_lconcat apply fast
    done
  done



lemma join_op_soundness:          
  "Data t tuple \<in> lset (produce (join_op [] [] {} join) lxs) \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   \<exists> d1 d2 . d1 \<in> set (data_list_at lxs (Inl t)) \<and> d2 \<in> set (data_list_at lxs (Inr t)) \<and>
   join d1 d2 = Some tuple"
  unfolding join_op_def produce_compose_op_correctness produce_map_op_correctness llist.set_map produce_flatten_op_correctness
  apply (drule union_op_Data_soundness)
  apply (auto simp add: image_iff split: event.splits)
  subgoal 
    apply (subst (asm) lset_lconcat)
    apply auto
    subgoal for x
      apply (cases x)
      subgoal for st d
        apply hypsubst_thin
        apply simp
        apply (subst (asm) in_lset_conv_lnth)
        apply (elim exE conjE)
        subgoal for n       
          apply (frule produce_multi_incr_op_soundness)
             apply assumption+
          apply simp
          apply (elim exE conjE)
          subgoal for m
            apply hypsubst_thin
            apply (cases st)
            subgoal for t'
              apply hypsubst_thin
              apply (subgoal_tac "concat (map snd (ltaken_Data m (produce (sync_op []) lxs))) \<noteq> []")
               defer
               apply (smt (verit, ccfv_SIG) empty_iff image_is_empty join_list_neq_Nil_D set_empty2)
              apply (subgoal_tac "tuple \<in> set (join_list join (Inl t') (concat (map snd (ltaken_Data m (produce (sync_op []) lxs)))))")
               defer
               apply force
              apply (subgoal_tac "t = t'")
               defer
               apply fastforce
              apply (drule in_join_list_D)
               apply (rule refl)
              apply (elim exE conjE)
              subgoal for d1 d2
                apply (rule exI[of _ d1])
                apply (rule conjI)
                subgoal premises prems2
                  using prems2(1,7,8,9,10) apply -
                  apply auto
                  subgoal for t1 dd1 t2 dd2 t3 dd3
                    apply (cases m)
                     apply simp
                    subgoal for n
                      apply hypsubst_thin
                      using ltaken_Data_produce_soundness[where lxs=lxs and WM=WM and t="Inl t'" and t'="Inl t'" and wm=t3 and batch=dd3 and n=n and buf="[]"] apply simp
                      apply (drule meta_mp)
                       apply (metis fst_conv image_eqI ltaken_Data_produce_sync_op_in_batch_LE)
                      apply (drule meta_mp)
                       apply force
                      unfolding join_list_def Let_def coll_def coll_list_def map_filter_def
                      apply auto
                      apply (rule image_eqI[where b=d1 and f="\<lambda>x. the (get_Data x)" and x="Data (Inl t') d1"])
                       apply auto
                      apply (subst set_list_of)
                      subgoal
                        apply (cases "\<exists> d . Data (Inl t') d  \<in> lset lxs")
                        subgoal
                          apply (subgoal_tac "\<exists> wm . Watermark (Inl wm) \<in> lset lxs \<and> wm \<ge> t'")
                         apply (smt (verit, ccfv_SIG) Inl_leq dual_order.refl event.distinct(1) event.sel(1) event.split_sel le_boolE lfilter_cong nless_le strict_monotone_lfinite_lfilter_eq_t_alt)
                          apply (metis Inr_Inl_False fst_conv less_eq_sum.simps sum.inject(1))
                          done
                        subgoal
                          apply (metis (no_types, lifting) equals0D in_ltaken_Data_in_lxs list.set(1))
                          done
                        done
                      apply simp
                      using in_ltaken_Data_in_lxs apply (metis empty_iff list.set(1))
                      done
                    done
                  done
                apply (rule exI[of _ d2])
                subgoal premises prems2
                  using prems2(1,7,8,9,10) apply -
                  apply auto
                  subgoal for t1 dd1 t2 dd2 t3 dd3
                    apply (cases m)
                     apply simp
                    subgoal for n
                      apply hypsubst_thin
                      using ltaken_Data_produce_soundness[where lxs=lxs and WM=WM and t="Inr t'" and t'="Inr t'" and wm =t2 and batch=dd2 and n=n and buf="[]"] apply simp
                      apply (drule meta_mp)
                       apply (metis fst_conv image_eqI ltaken_Data_produce_sync_op_in_batch_LE)
                      apply (drule meta_mp)
                       apply force
                      unfolding join_list_def Let_def coll_def coll_list_def map_filter_def
                      apply auto
                      apply (rule image_eqI[where b=d2 and f="\<lambda>x. the (get_Data x)" and x="Data (Inr t') d2"])
                       apply auto
                        apply (subst set_list_of)
                      subgoal
                        apply (cases "\<exists> d . Data (Inr t') d  \<in> lset lxs")
                        subgoal
                          apply (subgoal_tac "\<exists> wm . Watermark (Inr wm) \<in> lset lxs \<and> wm \<ge> t'")
                          apply (smt (verit, ccfv_SIG) dual_order.refl event.distinct(1) event.inject(1) event.split_sel fst_conv le_boolD lfilter_cong nless_le strict_monotone_lfinite_lfilter_eq_t_alt)
                          apply (cases "t2")
                           apply (metis Inr_Inl_False fst_conv less_eq_sum.simps)
                          subgoal for x
                            apply (rule exI[of _ x])
                            apply simp
                            subgoal premises prems
                              using prems(5,9,10) apply -
                              apply (metis Inr_Inl_False fst_conv less_eq_sum.simps sum.inject(2))
                              done
                            done
                          done
                        apply simp
                        using in_ltaken_Data_in_lxs apply fastforce
                          done
                        subgoal
                          using in_ltaken_Data_in_lxs apply fastforce
                          done
                        done
                      done
                    using prems2(11) apply blast
                    done
                  done
                done
            subgoal for t'
              apply hypsubst_thin
              apply (subgoal_tac "concat (map snd (ltaken_Data m (produce (sync_op []) lxs))) \<noteq> []")
               defer
               apply (smt (verit, ccfv_SIG) empty_iff image_is_empty join_list_neq_Nil_D set_empty2)
              apply (subgoal_tac "tuple \<in> set (join_list join (Inl t') (concat (map snd (ltaken_Data m (produce (sync_op []) lxs)))))")
               defer
               apply force
              apply (subgoal_tac "t = t'")
               defer
               apply fastforce
              apply (drule in_join_list_D)
               apply (rule refl)
              apply (elim exE conjE)
              subgoal for d1 d2
                apply (rule exI[of _ d1])
                apply (rule conjI)
                subgoal premises prems2
                  using prems2(1,7,8,9,10) apply -
                  apply auto
                  subgoal for t1 dd1 t2 dd2 t3 dd3
                    apply (cases m)
                     apply simp
                    subgoal for n
                      apply hypsubst_thin
                      using ltaken_Data_produce_soundness[where lxs=lxs and WM=WM and t="Inl t'" and t'="Inl t'" and wm=t3 and batch=dd3 and n=n and buf="[]"] apply simp
                      apply (drule meta_mp)
                       apply (metis fst_conv image_eqI ltaken_Data_produce_sync_op_in_batch_LE)
                      apply (drule meta_mp)
                       apply force
                      unfolding join_list_def Let_def coll_def coll_list_def map_filter_def
                      apply auto
                      apply (rule image_eqI[where b=d1 and f="\<lambda>x. the (get_Data x)" and x="Data (Inl t') d1"])
                       apply auto
                      apply (subst set_list_of)
                      subgoal
                        apply (cases "\<exists> d . Data (Inl t') d  \<in> lset lxs")
                        subgoal
                          apply (subgoal_tac "\<exists> wm . Watermark (Inl wm) \<in> lset lxs \<and> wm \<ge> t'")
                         apply (smt (verit, ccfv_SIG) Inl_leq dual_order.refl event.distinct(1) event.sel(1) event.split_sel le_boolE lfilter_cong nless_le strict_monotone_lfinite_lfilter_eq_t_alt)
                          apply (metis Inr_Inl_False fst_conv less_eq_sum.simps sum.inject(1))
                          done
                        subgoal
                          apply (metis (no_types, lifting) equals0D in_ltaken_Data_in_lxs list.set(1))
                          done
                        done
                      apply simp
                      using in_ltaken_Data_in_lxs apply (metis empty_iff list.set(1))
                      done
                    done
                  done
                apply (rule exI[of _ d2])
                subgoal premises prems2
                  using prems2(1,7,8,9,10) apply -
                  apply auto
                  subgoal for t1 dd1 t2 dd2 t3 dd3
                    apply (cases m)
                     apply simp
                    subgoal for n
                      apply hypsubst_thin
                      using ltaken_Data_produce_soundness[where lxs=lxs and WM=WM and t="Inr t'" and t'="Inr t'" and wm =t2 and batch=dd2 and n=n and buf="[]"] apply simp
                      apply (drule meta_mp)
                       apply (metis fst_conv image_eqI ltaken_Data_produce_sync_op_in_batch_LE)
                      apply (drule meta_mp)
                       apply force
                      unfolding join_list_def Let_def coll_def coll_list_def map_filter_def
                      apply auto
                      apply (rule image_eqI[where b=d2 and f="\<lambda>x. the (get_Data x)" and x="Data (Inr t') d2"])
                       apply auto
                        apply (subst set_list_of)
                      subgoal
                        apply (cases "\<exists> d . Data (Inr t') d  \<in> lset lxs")
                        subgoal
                          apply (subgoal_tac "\<exists> wm . Watermark (Inr wm) \<in> lset lxs \<and> wm \<ge> t'")
                          apply (smt (verit, ccfv_SIG) dual_order.refl event.distinct(1) event.inject(1) event.split_sel fst_conv le_boolD lfilter_cong nless_le strict_monotone_lfinite_lfilter_eq_t_alt)
                          apply (cases "t2")
                           apply (metis Inr_Inl_False fst_conv less_eq_sum.simps)
                          subgoal for x
                            apply (rule exI[of _ x])
                            apply simp
                            subgoal premises prems
                              using prems(5,9,10) apply -
                              apply (metis Inr_Inl_False fst_conv less_eq_sum.simps sum.inject(2))
                              done
                            done
                          done
                        apply simp
                        using in_ltaken_Data_in_lxs apply fastforce
                          done
                        subgoal
                          using in_ltaken_Data_in_lxs apply fastforce
                          done
                        done
                      done
                    using prems2(11) apply blast
                    done
                  done
                done
              done
            done
          done
      subgoal for wm
        apply simp
        done
      done
    done
  subgoal 
    apply (subst (asm) lset_lconcat)
    apply auto
    subgoal for x
      apply (cases x)
      subgoal for st d
        apply hypsubst_thin
        apply simp
        apply (subst (asm) in_lset_conv_lnth)
        apply (elim exE conjE)
        subgoal for n       
          apply (frule produce_multi_incr_op_soundness)
             apply assumption+
          apply simp
          apply (elim exE conjE)
          subgoal for m
            apply hypsubst_thin
            apply (cases st)
            subgoal for t'
              apply hypsubst_thin
              apply (subgoal_tac "concat (map snd (ltaken_Data m (produce (sync_op []) lxs))) \<noteq> []")
               defer
               apply (smt (verit, ccfv_SIG) empty_iff image_is_empty join_list_neq_Nil_D set_empty2)
              apply (subgoal_tac "tuple \<in> set (join_list join (Inl t') (concat (map snd (ltaken_Data m (produce (sync_op []) lxs)))))")
               defer
               apply force
              apply (subgoal_tac "t = t'")
               defer
               apply fastforce
              apply (drule in_join_list_D)
               apply (rule refl)
              apply (elim exE conjE)
              subgoal for d1 d2
                apply (rule exI[of _ d1])
                apply (rule conjI)
                subgoal premises prems2
                  using prems2(1,7,8,9,10) apply -
                  apply auto
                  subgoal for t1 dd1 t2 dd2 t3 dd3
                    apply (cases m)
                     apply simp
                    subgoal for n
                      apply hypsubst_thin
                      using ltaken_Data_produce_soundness[where lxs=lxs and WM=WM and t="Inl t'" and t'="Inl t'" and wm=t3 and batch=dd3 and n=n and buf="[]"] apply simp
                      apply (drule meta_mp)
                       apply (metis fst_conv image_eqI ltaken_Data_produce_sync_op_in_batch_LE)
                      apply (drule meta_mp)
                       apply force
                      unfolding join_list_def Let_def coll_def coll_list_def map_filter_def
                      apply auto
                      apply (rule image_eqI[where b=d1 and f="\<lambda>x. the (get_Data x)" and x="Data (Inl t') d1"])
                       apply auto
                      apply (subst set_list_of)
                      subgoal
                        apply (cases "\<exists> d . Data (Inl t') d  \<in> lset lxs")
                        subgoal
                          apply (subgoal_tac "\<exists> wm . Watermark (Inl wm) \<in> lset lxs \<and> wm \<ge> t'")
                         apply (smt (verit, ccfv_SIG) Inl_leq dual_order.refl event.distinct(1) event.sel(1) event.split_sel le_boolE lfilter_cong nless_le strict_monotone_lfinite_lfilter_eq_t_alt)
                          apply (metis Inr_Inl_False fst_conv less_eq_sum.simps sum.inject(1))
                          done
                        subgoal
                          apply (metis (no_types, lifting) equals0D in_ltaken_Data_in_lxs list.set(1))
                          done
                        done
                      apply simp
                      using in_ltaken_Data_in_lxs apply (metis empty_iff list.set(1))
                      done
                    done
                  done
                apply (rule exI[of _ d2])
                subgoal premises prems2
                  using prems2(1,7,8,9,10) apply -
                  apply auto
                  subgoal for t1 dd1 t2 dd2 t3 dd3
                    apply (cases m)
                     apply simp
                    subgoal for n
                      apply hypsubst_thin
                      using ltaken_Data_produce_soundness[where lxs=lxs and WM=WM and t="Inr t'" and t'="Inr t'" and wm =t2 and batch=dd2 and n=n and buf="[]"] apply simp
                      apply (drule meta_mp)
                       apply (metis fst_conv image_eqI ltaken_Data_produce_sync_op_in_batch_LE)
                      apply (drule meta_mp)
                       apply force
                      unfolding join_list_def Let_def coll_def coll_list_def map_filter_def
                      apply auto
                      apply (rule image_eqI[where b=d2 and f="\<lambda>x. the (get_Data x)" and x="Data (Inr t') d2"])
                       apply auto
                        apply (subst set_list_of)
                      subgoal
                        apply (cases "\<exists> d . Data (Inr t') d  \<in> lset lxs")
                        subgoal
                          apply (subgoal_tac "\<exists> wm . Watermark (Inr wm) \<in> lset lxs \<and> wm \<ge> t'")
                          apply (smt (verit, ccfv_SIG) dual_order.refl event.distinct(1) event.inject(1) event.split_sel fst_conv le_boolD lfilter_cong nless_le strict_monotone_lfinite_lfilter_eq_t_alt)
                          apply (cases "t2")
                           apply (metis Inr_Inl_False fst_conv less_eq_sum.simps)
                          subgoal for x
                            apply (rule exI[of _ x])
                            apply simp
                            subgoal premises prems
                              using prems(5,9,10) apply -
                              apply (metis Inr_Inl_False fst_conv less_eq_sum.simps sum.inject(2))
                              done
                            done
                          done
                        apply simp
                        using in_ltaken_Data_in_lxs apply fastforce
                          done
                        subgoal
                          using in_ltaken_Data_in_lxs apply fastforce
                          done
                        done
                      done
                    using prems2(11) apply blast
                    done
                  done
                done
            subgoal for t'
              apply hypsubst_thin
              apply (subgoal_tac "concat (map snd (ltaken_Data m (produce (sync_op []) lxs))) \<noteq> []")
               defer
               apply (smt (verit, ccfv_SIG) empty_iff image_is_empty join_list_neq_Nil_D set_empty2)
              apply (subgoal_tac "tuple \<in> set (join_list join (Inr t') (concat (map snd (ltaken_Data m (produce (sync_op []) lxs)))))")
               defer
               apply force
              apply (subgoal_tac "t = t'")
               defer
               apply fastforce
              apply (drule in_join_list_D)
               apply (rule refl)
              apply (elim exE conjE)
              subgoal for d1 d2
                apply (rule exI[of _ d1])
                apply (rule conjI)
                subgoal premises prems2
                  using prems2(1,7,8,9,10) apply -
                  apply auto
                  subgoal for t1 dd1 t2 dd2 t3 dd3
                    apply (cases m)
                     apply simp
                    subgoal for n
                      apply hypsubst_thin
                      using ltaken_Data_produce_soundness[where lxs=lxs and WM=WM and t="Inl t'" and t'="Inl t'" and wm=t3 and batch=dd3 and n=n and buf="[]"] apply simp
                      apply (drule meta_mp)
                       apply (metis fst_conv image_eqI ltaken_Data_produce_sync_op_in_batch_LE)
                      apply (drule meta_mp)
                       apply force
                      unfolding join_list_def Let_def coll_def coll_list_def map_filter_def
                      apply auto
                      apply (rule image_eqI[where b=d1 and f="\<lambda>x. the (get_Data x)" and x="Data (Inl t') d1"])
                       apply auto
                      apply (subst set_list_of)
                      subgoal
                        apply (cases "\<exists> d . Data (Inl t') d  \<in> lset lxs")
                        subgoal
                          apply (subgoal_tac "\<exists> wm . Watermark (Inl wm) \<in> lset lxs \<and> wm \<ge> t'")
                         apply (smt (verit, ccfv_SIG) Inl_leq dual_order.refl event.distinct(1) event.sel(1) event.split_sel le_boolE lfilter_cong nless_le strict_monotone_lfinite_lfilter_eq_t_alt)
                          apply (metis Inr_Inl_False fst_conv less_eq_sum.simps sum.inject(1))
                          done
                        subgoal
                          apply (metis (no_types, lifting) equals0D in_ltaken_Data_in_lxs list.set(1))
                          done
                        done
                      apply simp
                      using in_ltaken_Data_in_lxs apply (metis empty_iff list.set(1))
                      done
                    done
                  done
                apply (rule exI[of _ d2])
                subgoal premises prems2
                  using prems2(1,7,8,9,10) apply -
                  apply auto
                  subgoal for t1 dd1 t2 dd2 t3 dd3
                    apply (cases m)
                     apply simp
                    subgoal for n
                      apply hypsubst_thin
                      using ltaken_Data_produce_soundness[where lxs=lxs and WM=WM and t="Inr t'" and t'="Inr t'" and wm =t2 and batch=dd2 and n=n and buf="[]"] apply simp
                      apply (drule meta_mp)
                       apply (metis fst_conv image_eqI ltaken_Data_produce_sync_op_in_batch_LE)
                      apply (drule meta_mp)
                       apply force
                      unfolding join_list_def Let_def coll_def coll_list_def map_filter_def
                      apply auto
                      apply (rule image_eqI[where b=d2 and f="\<lambda>x. the (get_Data x)" and x="Data (Inr t') d2"])
                       apply auto
                        apply (subst set_list_of)
                      subgoal
                        apply (cases "\<exists> d . Data (Inr t') d  \<in> lset lxs")
                        subgoal
                          apply (subgoal_tac "\<exists> wm . Watermark (Inr wm) \<in> lset lxs \<and> wm \<ge> t'")
                          apply (smt (verit, ccfv_SIG) dual_order.refl event.distinct(1) event.inject(1) event.split_sel fst_conv le_boolD lfilter_cong nless_le strict_monotone_lfinite_lfilter_eq_t_alt)
                          apply (cases "t2")
                           apply (metis Inr_Inl_False fst_conv less_eq_sum.simps)
                          subgoal for x
                            apply (rule exI[of _ x])
                            apply simp
                            subgoal premises prems
                              using prems(5,9,10) apply -
                              apply (metis Inr_Inl_False fst_conv less_eq_sum.simps sum.inject(2))
                              done
                            done
                          done
                        apply simp
                        using in_ltaken_Data_in_lxs apply fastforce
                          done
                        subgoal
                          using in_ltaken_Data_in_lxs apply fastforce
                          done
                        done
                      done
                    using prems2(11) apply blast
                    done
                  done
                done
              done
            done
          done
      subgoal for wm
        apply simp
        done
      done
    done
  done
  
lemma prefix_production_LE_lt_le:
  "prefix_production_LE op lxs m1 n1 \<Longrightarrow>
   prefix_production_LE op lxs m2 n2 \<Longrightarrow>
   m1 < m2 \<Longrightarrow>
   n1 \<le> n2"
  apply (induct op lxs m1 n1 arbitrary: m2 n2 rule: prefix_production_LE.induct)
  subgoal
    apply (erule prefix_production_LE.cases)
     apply auto
    done
  subgoal
    apply (erule prefix_production_LE.cases)
     apply auto
     apply (smt (verit, ccfv_SIG) diff_is_0_eq diffs0_imp_equal le_trans less_Suc_eq_0_disj less_or_eq_imp_le llist.inject nat_neq_iff old.prod.inject prefix_production_LE.cases)
    apply (erule prefix_production_LE.cases)
     apply auto
    done
  done

lemma prefix_concat:
  "prefix xs ys \<Longrightarrow> prefix (concat xs) (concat ys)"
  by (metis concat_append prefix_def)

lemma ltaken_Data_prefix:
 "n1 \<le> n2 \<Longrightarrow>
  prefix (ltaken_Data n1 lxs) (ltaken_Data n2 lxs)"
  apply (induct n1 arbitrary: n2 lxs)
   apply simp
  subgoal for n1 n2 lxs
    apply (cases lxs)
     apply simp_all
    subgoal for x lxs'
      apply (cases x)
       apply auto
      apply (smt (verit, best) Cons_prefix_Cons Suc_le_D Suc_le_mono ltaken_Data.simps(2))
      apply (simp add: ltaken_Data_LCons_Watermark)
      done
    done
  done

(* FIXME: move me*)
lemma incr_op_prefix_cases:
  "Data t1 batch1 \<in> lset (produce (incr_op buf) lxs) \<Longrightarrow>
   Data t2 batch2 \<in> lset (produce (incr_op buf) lxs) \<Longrightarrow>
   prefix batch1 batch2 \<or> prefix batch2 batch1"
  apply (simp add: in_lset_conv_lnth)
  apply (elim exE conjE)
  subgoal for n1 n2
    apply (cases "n1 < n2")
    subgoal
      apply (rule disjI1)
      using lnth_produce_prefix_production_EQ_Ex[where op="incr_op buf" and m=n1 and x="Data t1 batch1" and lxs=lxs] apply simp
      using lnth_produce_prefix_production_EQ_Ex[where op="incr_op buf" and m=n2 and x="Data t2 batch2" and lxs=lxs] apply simp
      apply (elim exE conjE)
      subgoal for k1 k2
        using produce_incr_op_soundness[of buf lxs n1 t1 batch1 "Suc k1"] apply simp
        using produce_incr_op_soundness[of buf lxs n2 t2 batch2 "Suc k2"] apply simp
        apply auto
        apply hypsubst_thin
        apply (subgoal_tac "Suc k1 \<le> Suc k2")
         defer
        using prefix_production_LE_lt_le apply blast
        apply (rule prefix_concat)
        apply (rule map_mono_prefix)
        using ltaken_Data_prefix apply blast
        done
      done
    subgoal
      apply (simp add: linorder_class.not_less order.order_iff_strict)
      apply (elim disjE)
      subgoal
        apply (rule disjI2)
        using lnth_produce_prefix_production_EQ_Ex[where op="incr_op buf" and m=n1 and x="Data t1 batch1" and lxs=lxs] apply simp
        using lnth_produce_prefix_production_EQ_Ex[where op="incr_op buf" and m=n2 and x="Data t2 batch2" and lxs=lxs] apply simp
        apply (elim exE conjE)
        subgoal for k1 k2
          using produce_incr_op_soundness[of buf lxs n1 t1 batch1 "Suc k1"] apply simp
          using produce_incr_op_soundness[of buf lxs n2 t2 batch2 "Suc k2"] apply simp
          apply auto
          apply hypsubst_thin
          apply (subgoal_tac "Suc k2 \<le> Suc k1")
           defer
          using prefix_production_LE_lt_le apply blast
          apply (rule prefix_concat)
          apply (rule map_mono_prefix)
          using ltaken_Data_prefix apply blast
          done
        done
      apply auto
      done
    done
  done

lemma multi_incr_op_prefix_cases:
  "Data t1 batch1 \<in> lset (produce (multi_incr_op buf1 buf2) lxs) \<Longrightarrow>
   Data t2 batch2 \<in> lset (produce (multi_incr_op buf1 buf2) lxs) \<Longrightarrow>
   prefix batch1 batch2 \<or> prefix batch2 batch1"
  unfolding  produce_compose_op_correctness multi_incr_op_def
  apply (drule incr_op_prefix_cases)
   apply auto
  done

lemma join_op_completeness:
  "(\<exists>i1 i2 d1 d2. enat i1 < llength lxs \<and> lnth lxs i1 = Data (Inl t) d1 \<and> j1 = Suc i1 \<and>
   enat i2 < llength lxs \<and> lnth lxs i2 = Data (Inr t) d2 \<and> j2 = Suc i2 \<and>
     join d1 d2 = Some tuple) \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   productive lxs \<Longrightarrow> 
   Data t tuple \<in> lset (produce (join_op [] [] W join) lxs) \<or> 
   (lfinite lxs \<and> (\<forall>k1\<in>{j1..<the_enat (llength lxs)}. \<forall>t'\<ge>t. lnth lxs k1 \<noteq> Watermark (Inl t'))) \<or>
   (lfinite lxs \<and> (\<forall>k2\<in>{j2..<the_enat (llength lxs)}. \<forall>t'\<ge>t. lnth lxs k2 \<noteq> Watermark (Inr t')))"
 unfolding produce_compose_op_correctness join_op_def 
  apply (elim exE conjE)
  subgoal for i1 i2 d1 d2
    using produce_multi_incr_op_completeness[where lxs=lxs and t="Inl t" and j=j1 and WM=WM, of "[]" "[]"] apply simp
    using produce_multi_incr_op_completeness[where lxs=lxs and t="Inr t" and j=j2 and WM=WM, of "[]" "[]"] apply simp
    apply (elim disjE exE)
    subgoal for batch1 batch2
      apply (rule disjI1)
      apply hypsubst_thin
      apply (subgoal_tac "(Inl t, d1) \<in> set batch1")
      defer
      subgoal
        using produce_multi_incr_op_soundness_alt[of "Inl t" batch1 "[]" "[]" lxs WM] apply simp
        apply (elim exE conjE)
        unfolding coll_list_def coll_def
        apply (drule spec[of _ "Inl t"])
        apply (drule mp)
         apply simp
        subgoal premises prems
          using prems(3,5,10) prems(12)[symmetric] apply (auto simp del: mset_map split: event.splits)
          apply hypsubst_thin
          apply (drule mset_eq_setD)
          apply simp
          unfolding List.map_filter_def
          apply simp
          apply (subst (asm) set_list_of)
          using prems(1,2)  apply (smt (verit, ccfv_threshold) dual_order.refl event.distinct(1) event.inject(1) event.split_sel le_boolD lfilter_cong nless_le strict_monotone_productive_lfinite_lfilter_eq_t)
          apply auto
          apply (subgoal_tac "Data (Inl t) d1 \<in> {x \<in> lset lxs. (\<forall>x11. (\<forall>x12. x \<noteq> Data x11 x12) \<or> x11 = Inl t) \<and> (\<forall>x2. x \<noteq> Watermark x2) \<and> (\<exists>y. get_Data x = Some y)}")
          defer
          using in_lset_conv_lnth prems(4) apply force
          apply (smt (verit, ccfv_threshold) event.simps(5) image_iff mem_Collect_eq option.sel prod.collapse)
          done
        done
      apply (subgoal_tac "(Inr t, d2) \<in> set batch2")
       defer
      subgoal
      using produce_multi_incr_op_soundness_alt[of "Inr t" batch2 "[]" "[]" lxs WM] apply simp
        apply (elim exE conjE)
        unfolding coll_list_def coll_def
        apply (drule spec[of _ "Inr t"])
        apply (drule mp)
         apply simp
        subgoal premises prems
          using prems(6,7,11) prems(13)[symmetric] apply (auto simp del: mset_map split: event.splits)
          apply hypsubst_thin
          apply (drule mset_eq_setD)
          apply simp
          unfolding List.map_filter_def
          apply simp
          apply (subst (asm) set_list_of)
          using prems(1,2)  apply (smt (verit, ccfv_threshold) dual_order.refl event.distinct(1) event.inject(1) event.split_sel le_boolD lfilter_cong nless_le strict_monotone_productive_lfinite_lfilter_eq_t)
          apply auto
          apply (subgoal_tac "Data (Inr t) d2 \<in> {x \<in> lset lxs. (\<forall>x11. (\<forall>x12. x \<noteq> Data x11 x12) \<or> x11 = Inr t) \<and> (\<forall>x2. x \<noteq> Watermark x2) \<and> (\<exists>y. get_Data x = Some y)}")
          defer
          using in_lset_conv_lnth prems(5) apply force
          apply (smt (verit, ccfv_threshold) event.simps(5) image_iff mem_Collect_eq option.sel prod.collapse)
          done
        done
      unfolding produce_map_op_correctness produce_flatten_op_correctness
      apply (auto split: event.splits)
      apply (frule multi_incr_op_prefix_cases[of _ batch1 _ _ _ _ batch2])
      apply assumption+           
      apply (elim disjE)
      subgoal
      apply (rule produce_union_op_Inr_completeness)
      apply (subst lset_lconcat)
        apply auto
        apply (rule bexI[of _ "Data (Inr t) batch2"])
        apply auto
        using in_join_list_Inr set_mono_prefix apply fastforce
        done
     subgoal
      apply (rule produce_union_op_Inl_completeness)
      apply (subst lset_lconcat)
        apply auto
        apply (rule bexI[of _ "Data (Inl t) batch1"])
        apply auto
        using in_join_list_Inl set_mono_prefix apply fastforce
        done
      done 
    subgoal for batch1 
      apply simp
      apply (rule disjI2)
      apply (rule disjI2)
      using Inr_leq apply blast
      done
    subgoal for batch2
      apply simp
      apply (rule disjI2)
      apply (rule disjI1)
      using Inl_leq apply blast
      done
    subgoal
      apply simp
      apply (rule disjI2)
      apply (rule disjI1)
      using Inl_leq apply blast
      done
    done
  done


end