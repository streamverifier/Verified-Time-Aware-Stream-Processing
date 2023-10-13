theory Logic_on_Watermarked_Stream
  imports
    "Watermarked_Stream"
    "Logic_on_Llists"
    "Sum_Order"
begin

section \<open>sync_op\<close> 
primcorec sync_op :: "('t::order \<times> 'd) list \<Rightarrow> (('t, ('t \<times> 'd) list) event, ('t, 'd) event) op" where
  "sync_op buf = Logic (\<lambda> ev.
     case ev of
       Data t d \<Rightarrow> (sync_op (buf @ [(t, d)]), [])
     | Watermark wm \<Rightarrow> if \<exists> (t, d) \<in> set buf . t \<le> wm
                        then let out = filter (\<lambda> (t, _) . t \<le> wm) buf ;
                                 buf' = filter (\<lambda> (t, _) . \<not> t \<le> wm) buf in
                                 (sync_op buf', [Data wm out, Watermark wm])
                        else (sync_op buf, [])
  )"

subsection \<open>Auxiliary lemmas\<close> 
lemma sync_op_buf_order_empty_lgc_preserves:
  "apply (sync_op buf) h = (lgc1, []) \<Longrightarrow>
   (\<exists> wm. h = Watermark wm \<and> lgc1 = (sync_op buf) \<and> \<not> (\<exists> (t, d) \<in> set buf . t \<le> wm)) \<or> (\<exists> t d . h = Data t d \<and> lgc1 = (sync_op (buf @ [(t,d)])))"
  apply (auto split: event.splits prod.splits list.splits if_splits)
  done

lemma sync_op_buf_some_out_lgc_preserves:
  "apply (sync_op buf) h = (lgc1, x#xs) \<Longrightarrow>
   \<exists> wm d. h = Watermark wm \<and> (\<exists> (t, d) \<in> set buf . t \<le> wm) \<and> lgc1 = (sync_op (filter  (\<lambda> (t, _) . \<not> t \<le> wm) buf)) \<and> x = Data wm d \<and> xs = [Watermark wm]"
  apply (auto split: event.splits prod.splits list.splits if_splits)
  done

lemma produce_lhd_data:
  "lhd' lxs = Some (Data t d) \<Longrightarrow>
   produce (sync_op (buf @ [(t, d)])) (ltl lxs) = produce (sync_op buf) lxs"
  apply (subst (2) produce.code)
  apply (subst produce_inner.simps)
  apply (auto split: llist.splits event.splits option.splits)
  subgoal
    apply (subst produce.code)
    apply simp
    done
  done

lemma produce_inner_Some_inversion:
  "produce_inner (sync_op buf, lxs) = Some (op, x, xs', lxs') \<Longrightarrow>
   \<exists> n wm t d. wm \<ge> t \<and> lnth lxs n = Watermark wm \<and> n < llength lxs \<and> ((t, d) \<in> set buf \<or> Data t d \<in> lset (ltake (enat n) lxs))"
  apply (induct "(sync_op buf, lxs)" "(op, x, xs', lxs')" arbitrary: buf lxs rule: produce_inner_alt[consumes 1])
  subgoal for h lxs' lgc' buf
    apply (frule sync_op_buf_order_empty_lgc_preserves)
    apply (elim conjE disjE exE)
    subgoal for wm
      apply hypsubst_thin
      subgoal premises p2
        using p2(2)[where buf="buf"] apply -
        using p2(1) apply -
        apply (drule meta_mp)
         apply (rule refl)
        apply (elim conjE disjE exE)
        subgoal for n wm t' d'
          apply (metis in_lset_conv_lnth llist.set_intros(2))
          done
        subgoal for n wm t' d'
          apply (metis Extended_Nat.eSuc_mono eSuc_enat llength_LCons llist.set_intros(2) lnth_Suc_LCons ltake_eSuc_LCons)
          done
        done
      done
    subgoal for t d
      apply hypsubst_thin
      subgoal premises p2
        using p2(2)[where buf="buf @ [(t, d)]"] apply -
        using p2(1) apply -
        apply (drule meta_mp)
         apply (rule refl)
        apply (elim conjE disjE exE)
        subgoal for n wm t' d'
          apply (rule exI[of _ "Suc n"])
          apply (rule exI[of _ wm])
          apply (metis Suc_ile_eq Un_iff eSuc_enat empty_iff empty_set fst_conv iless_Suc_eq llength_LCons llist.set_intros(1) lnth_Suc_LCons ltake_eSuc_LCons set_ConsD set_append)
          done
        subgoal for n wm t' d'
          apply (rule exI[of _ "Suc n"])
          apply (rule exI[of _ wm])
          apply (metis Extended_Nat.eSuc_mono eSuc_enat llength_LCons llist.set_intros(2) lnth_Suc_LCons ltake_eSuc_LCons)
          done
        done
      done
    done
  subgoal for h buf
    apply (frule sync_op_buf_some_out_lgc_preserves)
    apply (elim conjE disjE exE)
    subgoal for wm
      apply (metis (no_types, lifting) case_prodE in_lset_conv_lnth llist.set_intros(1))
      done
    done
  done

lemma produce_inner_conditions_to_produce_aux:
  "x \<in> lset lxs \<Longrightarrow>
   x = Watermark wm \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   wm \<ge> t \<Longrightarrow>
   n < llength lxs \<Longrightarrow>
   lnth lxs n = Watermark wm \<Longrightarrow>
   ((t, d) \<in> set buf \<or> (lnth lxs m = Data t d \<and> m < n)) \<Longrightarrow>
   \<exists> buf' wm' batch lxs' . produce_inner (sync_op buf, lxs) = Some (sync_op buf', Data wm' batch, [Watermark wm'], lxs') \<and> \<not> wm' > wm \<and> (n = 0 \<longrightarrow> (t, d) \<in> set buf \<longrightarrow> (t, d) \<in> set batch)"
  apply (induct lxs arbitrary: buf n m t d rule: lset_induct)
  subgoal for xs buf
    apply hypsubst_thin
    apply (elim disjE)
    subgoal
      apply (subst produce_inner.simps)
      apply (auto simp del: sync_op.simps split: prod.splits list.splits llist.splits event.splits option.splits)
        apply (smt (verit, best) case_prodI event.simps(6) list.simps(3) prod.simps(1) sync_op.sel)
      using sync_op_buf_some_out_lgc_preserves apply blast
      apply (frule sync_op_buf_some_out_lgc_preserves)
      apply (elim exE conjE)
      subgoal for x1 x21 x22 wm' d'
        apply (rule exI[of _ wm'])
        apply (rule exI[of _ d'])
        apply (rule conjI)
         apply simp
        apply (rule conjI)
         apply simp
        apply safe
        apply hypsubst_thin
        apply (smt (verit, ccfv_threshold) Pair_inject case_prodI event.inject(1) event.simps(6) list.inject mem_Collect_eq set_filter sync_op.simps)
        done
      done
    subgoal
      by (metis Suc_ile_eq diff_Suc_1 dual_order.refl iless_Suc_eq in_lset_conv_lnth less_imp_Suc_add llength_LCons lnth_LCons' not_less_zero tail_incomparable)
    done
  subgoal for x' xs buf n m t d
    apply hypsubst_thin
    apply (subgoal_tac "n \<noteq> 0")
     defer
     apply (metis lnth_0)
    apply (subst produce_inner.simps)
    apply (auto  split: event.splits prod.splits list.splits llist.splits option.splits)
    subgoal premises p for t' d'
      using p(1,3-) apply -
      using p(2)[where t=t and n="n - 1" and d=d and buf="buf @ [(t', d')]"] apply -
      apply (drule meta_spec)+
      apply (drule meta_mp)
      using strict_monotone_drop_head apply blast
      apply (drule meta_mp)
       apply assumption+
      apply (drule meta_mp)
       apply (metis Suc_diff_1 Suc_ile_eq)
      apply (drule meta_mp)
       apply (simp add: lnth_LCons')
      apply (drule meta_mp)
       apply (rule disjI1)
       apply simp
      apply blast
      done
    subgoal
      using order_less_imp_le tail_incomparable by blast
    subgoal
      by (meson in_lset_conv_lnth strict_monotone_drop_head)
    subgoal premises p for t' d'
      using p(1,3-) apply -
      using p(2)[where t=t and n="n - 1" and buf="buf @ [(t', d')]" and m="m - 1" and d=d] apply -
      apply (drule meta_mp)
      using strict_monotone_drop_head apply blast
      apply (drule meta_mp)
       apply assumption+
      apply (drule meta_mp)
       apply (simp add: dual_order.strict_trans1)
      apply (drule meta_mp)
       apply (simp add: lnth_LCons')
      apply (drule meta_mp)
       apply (metis Suc_pred' Un_iff event.inject(1) linorder_less_linear list.set_intros(1) lnth_LCons' nat_add_left_cancel_less not_less0 plus_1_eq_Suc set_append)
      apply blast
      done
    subgoal
      using order_less_imp_le tail_incomparable by blast
    subgoal premises p for wm'
      using p(1,3-) apply -
      using  p(2)[where t=t and n="n - 1" and m="m - 1" and d=d and buf=buf] apply -
      apply (drule meta_mp)
       apply (meson strict_monotone_drop_head)
      apply (metis (no_types, lifting) One_nat_def Suc_ile_eq Suc_less_eq Suc_pred bot_nat_0.not_eq_extremum event.distinct(1) event.inject(2) lnth_LCons')
      done
    done
  done

lemma produce_inner_conditions_to_produce:
  "monotone lxs WM \<Longrightarrow>
   wm \<ge> t \<Longrightarrow>
   n < llength lxs \<Longrightarrow>
   lnth lxs n = Watermark wm \<Longrightarrow>
   ((t, d) \<in> set buf \<or> (lnth lxs m = Data t d \<and> m < n)) \<Longrightarrow>
   \<exists> buf' wm' batch lxs' . produce_inner (sync_op buf, lxs) = Some (sync_op buf', Data wm' batch, [Watermark wm'], lxs') \<and>
   \<not> wm' > wm \<and> (n = 0 \<longrightarrow> (t, d) \<in> set buf \<longrightarrow> (t, d) \<in> set batch)"
  apply (rule produce_inner_conditions_to_produce_aux)
        defer
        apply (rule refl)
       apply assumption+
  by (metis in_lset_conv_lnth)

lemma produce_inner_sync_op_specify_Some:
  "produce_inner (sync_op buf, lxs) = Some (op, x, xs, lxs') \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   \<exists> buf' wm d lxs'. produce_inner (sync_op buf, lxs) = Some (sync_op buf', Data wm d, [Watermark wm], lxs')"
  apply (frule produce_inner_Some_inversion)
  using produce_inner_conditions_to_produce
  by (smt (verit, ccfv_SIG) enat_ord_simps(2) in_lset_conv_lnth llength_ltake lnth_ltake min_def order_less_imp_le)

lemma not_in_buf_produce_Watermark:
  "\<not> (\<exists> (t, d) \<in> set buf . t \<le> wm) \<Longrightarrow>
   produce (sync_op buf) (LCons (Watermark wm) lxs) = produce (sync_op buf) lxs"
  apply (subst (1 2) produce.code)
  apply (subst (1) produce_inner.simps)
  apply (auto split: llist.splits event.splits prod.splits list.splits option.splits)
  done

lemma produce_Data:
  "produce (sync_op buf) (LCons (Data t d) lxs) = produce (sync_op (buf@[(t, d)])) lxs"
  apply (subst (1 2) produce.code)
  apply (subst (1) produce_inner.simps)
  apply (auto split: llist.splits event.splits prod.splits list.splits option.splits)
  done

lemma produce_inner_sync_op_inversion:
  "produce_inner (sync_op buf, lxs) = Some (lgc', x, xs', lxs') \<Longrightarrow> \<exists> buf' n . lgc' = sync_op buf' \<and> lxs' = ldropn n lxs \<and> n > 0"
  subgoal premises prems
    using prems apply -
    apply (induct "(sync_op buf, lxs)" "(lgc', x, xs', lxs')" arbitrary: buf lxs rule: produce_inner_alt)
    using prems apply simp
    subgoal for h lxs'a lgc'a buf
      apply (subst (asm) (2) produce_inner.simps)
      apply (simp split: llist.splits event.splits)
      subgoal for  t d
        apply hypsubst_thin
        apply (drule meta_spec)+
        apply (drule meta_mp)
         apply (rule refl)
        apply (drule meta_mp)
         apply assumption
        apply (metis ldropn_Suc_LCons zero_less_Suc)
        done
      subgoal for wm
        apply (simp split: if_splits prod.splits)
        apply (metis ldropn_Suc_LCons zero_less_Suc)
        done
      done
    subgoal for h buf
      apply (subst (asm) produce_inner.simps)
      apply (simp split: llist.splits event.splits if_splits)
      apply (metis ldropn_0 ldropn_Suc_LCons zero_less_Suc)
      done
    done
  done

lemma produce_inner_sync_op_inversion_2:
  "produce_inner (sync_op buf, lxs) = Some (lgc', x, xs', lxs') \<Longrightarrow> \<exists> buf' . lgc' = sync_op buf'"
  using produce_inner_sync_op_inversion by blast

lemma produce_inner_skip_n_productions_op_sync_op_Some_batch:
  "produce_inner (skip_n_productions_op (sync_op buf) n, lxs) = Some (op, x, xs, lxs') \<Longrightarrow>
   \<exists> wm batch. x = Data wm batch \<and> xs = [Watermark wm] \<or> x = Watermark wm \<and> xs = []"
  apply (induct "(skip_n_productions_op (sync_op buf) n, lxs)" "(op, x, xs, lxs')" arbitrary: op buf lxs n rule: produce_inner_alt[consumes 1])
  subgoal
    apply (auto split: event.splits if_splits)
      apply (metis skip_n_productions_op_0)+
    done
  subgoal
    apply (auto split: event.splits if_splits)
    apply (metis drop_Cons' drop_Nil list.discI list.inject)
    done
  done

lemma produce_skip_n_productions_op_sync_op_n_Data_Suc_n_Watermark:
  "enat n < llength (produce (skip_n_productions_op (sync_op buf) i) lxs) \<Longrightarrow>
   lnth (produce (skip_n_productions_op (sync_op buf) i) lxs) n = Data wm batch \<Longrightarrow>
   lnth (produce (skip_n_productions_op (sync_op buf) i) lxs) (Suc n) = Watermark wm"
  apply (induct n arbitrary: i buf wm batch lxs)
  subgoal for i buf wm batch lxs
    apply (subst produce.code)
    apply (subst (asm) (1 2) produce.code)
    apply (auto split: option.splits)
    subgoal for op xs lxs'
      using produce_inner_skip_n_productions_op_sync_op_Some_batch[where n=i] apply simp
      apply (subst lnth_shift)
       apply blast
      apply fastforce
      done
    done
  subgoal for n buf wm batch
    apply (subst produce.code)
    apply (subst (asm) (4 5) produce.code)
    apply (auto split: option.splits)
    apply (metis (mono_tags, lifting) Suc_ile_eq produce_inner_Some_produce produce_skip_n_productions_op_LCons)
    done
  done

lemma produce_inner_skip_n_productions_op_Some_Data_Watermark_in:
  "produce_inner (skip_n_productions_op (sync_op buf) n, lxs) = Some (lgc', x, xs, lxs') \<Longrightarrow>
   x = Data wm batch \<Longrightarrow>
   Watermark wm \<in> lset lxs"
  apply (induct "(skip_n_productions_op (sync_op buf) n, lxs)" "(lgc', x, xs, lxs')" arbitrary: n buf lxs lxs' xs batch wm lgc' rule: produce_inner_alt[consumes 1])
  subgoal for h lxs' lgc' n buf lxs'a xs lgc'a batch wm
    apply (auto split: if_splits event.splits)
      apply (metis skip_n_productions_op_0)+
    done
  subgoal for h xs lxs' lgc' n buf batch wm
    apply hypsubst_thin
    apply (auto split: if_splits event.splits)
    apply (subgoal_tac "n = 1 \<or> n = 0")
     defer
     apply (metis (mono_tags, lifting) One_nat_def Suc_lessI add.commute bot_nat_0.not_eq_extremum drop_eq_Nil2 leI list.discI list.size(3) list.size(4) plus_1_eq_Suc)
    apply (elim disjE)
     apply (auto split: if_splits event.splits)
    done
  done

lemma produce_skip_n_productions_op_Some_Data_Watermark_in_LCons:
  "produce (skip_n_productions_op (sync_op buf) n) lxs = LCons x xs \<Longrightarrow>
   x = Data wm batch \<Longrightarrow>
   Watermark wm \<in> lset lxs"
  apply (subst (asm) produce.code)
  apply (auto simp add: produce_inner_skip_n_productions_op_Some_Data_Watermark_in split: option.splits)
  done

lemma produce_inner_sync_op_Watermark_in:
  "produce_inner (sync_op buf, lxs) = Some (op, x, xs, lxs') \<Longrightarrow>
   x = Data wm batch \<Longrightarrow>
   xs = [Watermark wm] \<Longrightarrow>
   Watermark wm \<in> lset lxs"
  apply (induct "(sync_op buf, lxs)" "(op, x, xs, lxs')" arbitrary: lxs lxs' op buf wm batch x xs rule: produce_inner_alt[consumes 1])
  subgoal for h lxs' lgc' lxs'a op buf x xs wm batch
    apply (auto split: event.splits if_splits)
    done
  subgoal for h x xs lxs' lgc' buf wm batch
    apply (auto split: event.splits if_splits)
    done
  done

lemma produce_inner_skip_n_productions_op_in_ts_or_buf:
  "produce_inner (skip_n_productions_op (sync_op buf) n, lxs) = Some (op, x, xs, lxs') \<Longrightarrow>
   x = Data wm batch \<Longrightarrow>
   xs = [Watermark wm] \<Longrightarrow>
   t' \<le> wm \<Longrightarrow>
   t' \<in> fst ` set batch \<Longrightarrow>
   \<exists> wm' \<ge> wm . Watermark wm' \<in> lset lxs \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   t' \<in> ts lxs wm \<or> t' \<in> fst ` set buf"
  subgoal premises prems
    using prems apply -
    apply (induct "(skip_n_productions_op (sync_op buf) n, lxs)" "(op, x, xs, lxs')" arbitrary: lxs lxs' op buf x xs n rule: produce_inner_alt)
    using prems apply simp
    subgoal for h lxs' lgc' lxs'' op buf x xs n
      apply (simp split: event.splits if_splits)
      subgoal for t'' d
        apply (drule meta_spec)+
        apply (drule meta_mp)
         apply hypsubst_thin
         apply (rule refl)
        apply (drule meta_mp)
        subgoal
          apply (subst (asm) produce_inner.simps)
          apply auto
          done
        apply (drule meta_mp)
        using strict_monotone_drop_head apply blast
        apply (metis (no_types, lifting) Un_iff append.right_neutral fst_conv image_Un image_insert insert_iff list.simps(15) set_append strict_monotone_drop_head)
        done
      subgoal
        apply (drule meta_spec)
        apply (drule meta_spec[of _ 0])
        apply (drule meta_mp)
         apply hypsubst_thin
         apply simp
        apply (drule meta_mp)
        subgoal
          apply (subst (asm) produce_inner.simps)
          apply auto
          done
        apply (drule meta_mp)
        using strict_monotone_drop_head apply blast
        using Un_iff append.right_neutral dual_order.refl fst_conv image_iff in_ts_LCons_LE set_ConsD set_append strict_monotone_drop_head ts_LCons
        apply (smt (verit, del_insts))
        done
      subgoal for wm
        apply (elim disjE)
        subgoal
          apply hypsubst_thin
          apply (drule meta_spec)+
          apply (drule meta_mp)
           apply (rule refl)
          apply (drule meta_mp)
          subgoal
            apply (subst (asm) produce_inner.simps)
            apply auto
            done
          apply (drule meta_mp)
           apply (subst (asm) produce_inner.simps)
           apply (auto split: option.splits)
          using produce_inner_skip_n_productions_op_Some_Data_Watermark_in apply blast
          using strict_monotone_drop_head apply fastforce
          done
        subgoal
          apply hypsubst_thin
          apply (drule meta_spec)+
          apply (drule meta_mp)
           apply (rule refl)
          apply (drule meta_mp)
          subgoal
            apply (subst (asm) produce_inner.simps)
            apply auto
            done
          apply (drule meta_mp)
           apply (subst (asm) produce_inner.simps)
           apply (auto split: option.splits)
          apply (metis (no_types, lifting) image_iff mem_Collect_eq strict_monotone_drop_head)
          done
        done
      subgoal for wm
        apply (elim disjE)
        subgoal
          apply hypsubst_thin
          apply (drule meta_spec)+
          apply (drule meta_mp)
           apply (rule refl)
          apply (drule meta_mp)
          subgoal
            apply (subst (asm) produce_inner.simps)
            apply auto
            done
          apply (drule meta_mp)
           apply (subst (asm) produce_inner.simps)
           apply (auto split: option.splits)
          using produce_inner_skip_n_productions_op_Some_Data_Watermark_in apply blast
          using strict_monotone_drop_head apply fastforce
          done
        subgoal
          apply hypsubst_thin
          apply (drule meta_spec)+
          apply (drule meta_mp)
           apply (rule refl)
          apply (drule meta_mp)
          subgoal
            apply (subst (asm) produce_inner.simps)
            apply auto
            done
          apply (drule meta_mp)
           apply (subst (asm) produce_inner.simps)
           apply (auto split: option.splits)
          apply (metis (no_types, lifting)  strict_monotone_drop_head)
          done
        done
      subgoal for wm
        apply (elim disjE)
        subgoal
          apply hypsubst_thin
          apply (drule meta_spec)
          apply (drule meta_spec[of _ 0])
          apply (drule meta_mp)
           apply simp
          apply (drule meta_mp)
          subgoal
            apply (subst (asm) produce_inner.simps)
            apply auto
            done
          apply (drule meta_mp)
           apply (subst (asm) produce_inner.simps)
           apply (auto split: option.splits)
          using produce_inner_sync_op_Watermark_in apply blast
          using strict_monotone_drop_head apply fastforce
          done
        subgoal
          apply hypsubst_thin
          apply (drule meta_spec)
          apply (drule meta_spec[of _ 0])
          apply (drule meta_mp)
           apply simp
          apply (drule meta_mp)
          subgoal
            apply (subst (asm) produce_inner.simps)
            apply auto
            done
          apply (drule meta_mp)
           apply (subst (asm) produce_inner.simps)
           apply (auto split: option.splits)
          apply (metis (no_types, lifting) image_iff mem_Collect_eq strict_monotone_drop_head)
          done
        done
      subgoal for wm
        apply (elim disjE)
        subgoal
          apply hypsubst_thin
          apply (drule meta_spec)
          apply (drule meta_spec[of _ 0])
          apply (drule meta_mp)
           apply simp
          apply (drule meta_mp)
          subgoal
            apply (subst (asm) produce_inner.simps)
            apply auto
            done
          apply (drule meta_mp)
           apply (subst (asm) produce_inner.simps)
           apply (auto split: option.splits)
          using produce_inner_sync_op_Watermark_in apply blast
          using strict_monotone_drop_head apply fastforce
          done
        subgoal
          apply hypsubst_thin
          apply (drule meta_spec)
          apply (drule meta_spec[of _ 0])
          apply (drule meta_mp)
           apply simp
          apply (drule meta_mp)
          subgoal
            apply (subst (asm) produce_inner.simps)
            apply auto
            done
          apply (drule meta_mp)
           apply (subst (asm) produce_inner.simps)
           apply (auto split: option.splits)
          apply (metis (no_types, lifting) strict_monotone_drop_head)
          done
        done
      done
    subgoal for h x xs lxs' lgc' buf n
      apply (auto split: event.splits if_splits)
       apply (subgoal_tac "n = 0")
        apply force
       apply (metis drop_Cons' drop_Nil list.discI)
      apply (smt (z3) One_nat_def Suc_eq_plus1 diff_add_0 diff_diff_cancel drop_Cons' event.inject(1) filter_is_subset image_mono in_mono length_drop linorder_le_less_linear list.size(3) list.size(4) nth_Cons_0 plus_1_eq_Suc prems(5))
      done 
    done
  done

lemma in_buf_produce_Watermark:
  "\<exists> (t, d) \<in> set buf . t \<le> wm \<Longrightarrow>
   produce (sync_op buf) (LCons (Watermark wm) lxs) = LCons (Data wm (filter (\<lambda> (t, d) . t \<le> wm) buf)) (LCons (Watermark wm) ((produce (sync_op (filter (\<lambda>(t, _). \<not> t \<le> wm) buf)) lxs)))"
  apply (subst produce.code)
  apply (subst produce_inner.simps)
  apply (simp split: prod.splits list.splits option.splits)
  done

lemma produce_inner_skip_n_productions_op_sync_op_xs:
  "produce_inner (skip_n_productions_op (sync_op buf) n, lxs) = Some (op, x, xs, lxs') \<Longrightarrow>
  x = Data wm batch \<Longrightarrow>
  xs = [Watermark wm]"
  apply (induct "(skip_n_productions_op (sync_op buf) n, lxs)" "(op, x, xs, lxs')" arbitrary: lxs lxs' op buf x xs n rule: produce_inner_alt[consumes 1])
  subgoal for h lxs' lgc' lxs'a op buf x xs n
    apply (auto simp add:  in_buf_produce_Watermark split: event.splits if_splits)
      apply (metis skip_n_productions_op_0)+
    done
  subgoal for h x xs lxs' lgc' buf n
    apply (auto simp add: in_buf_produce_Watermark split: event.splits if_splits)
    apply (smt (verit, ccfv_threshold) drop_Cons' drop_eq_Nil2 event.distinct(1) event.inject(1) leI length_Cons less_Suc0 list.inject list.size(3))
    done
  done

lemma produce_skip_n_productions_op_sync_op_in_ts_or_buf:
  "produce (skip_n_productions_op (sync_op buf) n) lxs = LCons (Data wm batch) lxs' \<Longrightarrow>
   \<exists> wm' \<ge> wm . Watermark wm' \<in> lset lxs \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   t' \<le> wm \<Longrightarrow>
   t' \<in> fst ` set batch \<Longrightarrow> t' \<in> ts lxs wm \<or> t' \<in> fst ` set buf"
  apply (subst (asm) produce.code)
  apply (simp split: prod.splits option.splits)
  apply (rule produce_inner_skip_n_productions_op_in_ts_or_buf)
        apply assumption+
       apply (rule refl)
      apply (meson produce_inner_skip_n_productions_op_sync_op_xs)
     apply assumption+
   apply blast
  apply simp
  done

lemma produce_inner_inner_skip_n_productions_sync_op_batch_le:
  "produce_inner (skip_n_productions_op (sync_op buf) n, lxs) = Some (op, x, xs, lxs') \<Longrightarrow>
   x = Data wm batch \<Longrightarrow>
   xs = [Watermark wm] \<Longrightarrow>
  t \<in> fst ` set batch \<Longrightarrow>
   t \<le> wm"
  apply (induct "(skip_n_productions_op (sync_op buf) n, lxs)" "(op, x, xs, lxs')" arbitrary: lxs lxs' op buf x xs n rule: produce_inner_alt[consumes 1])
  subgoal
    apply (auto split: if_splits event.splits)
      apply (metis skip_n_productions_op_0)+
    done
  subgoal
    apply (auto split: if_splits event.splits)
    apply (metis (mono_tags, lifting) case_prod_unfold drop0 drop_Suc_Cons event.inject(1) fst_conv less_2_cases list.discI list.inject mem_Collect_eq not_less_iff_gr_or_eq numeral_2_eq_2 set_filter)
    done
  done

lemma produce_inner_skip_n_productions_op_sync_op_t_NOT_LE_Watermark:
  "produce_inner (skip_n_productions_op (sync_op (filter (\<lambda> (t, d) . \<not> t \<le> wm') buf)) n, lxs) = Some (op, x, xs, lxs') \<Longrightarrow>
   x = Data wm batch \<Longrightarrow>
   xs = [Watermark wm] \<Longrightarrow>
   t \<in> fst ` set batch \<Longrightarrow>
   monotone lxs (insert wm' WM) \<Longrightarrow>
   \<not> t \<le> wm'"
  apply (induct "(skip_n_productions_op (sync_op (filter (\<lambda> (t, d) . \<not> t \<le> wm') buf)) n, lxs)" "(op, x, xs, lxs')" arbitrary: lxs lxs' op buf x xs n rule: produce_inner_alt[consumes 1])
  subgoal for h lxs' lgc' lxs'a op buf x xs n
    apply (auto split: if_splits event.splits)
    subgoal for t' d b
      apply (drule meta_spec[of _ "buf @ [(t', d)]"])
      apply (drule meta_spec[of _ n])
      apply (drule meta_mp)
       apply simp
       apply (meson LConsData insertI1)
      apply (drule meta_mp)
      using strict_monotone_drop_head apply blast
      apply simp
      done
    subgoal for wm'' a b aa ba bb
      apply hypsubst_thin
      apply (drule meta_spec[of _ "filter (\<lambda> (t, d) . \<not> t \<le> wm'') buf"])
      apply (drule meta_spec[of _ "n - Suc (Suc 0)"])
      apply (drule meta_mp)
       apply simp
       apply (meson LConsData insertI1)
      apply (drule meta_mp)
      using strict_monotone_drop_head apply blast
      apply simp
      done
    subgoal
      using strict_monotone_drop_head by blast
    subgoal for t' d b
      apply (drule meta_spec[of _ "buf @ [(t', d)]"])
      apply (drule meta_spec[of _ n])
      apply (drule meta_mp)
       apply simp
       apply (meson LConsData insertI1)
      apply (drule meta_mp)
      using strict_monotone_drop_head apply blast
      apply simp
      done
    subgoal for wm'' t' d b
      apply hypsubst_thin
      apply (drule meta_spec[of _ "filter (\<lambda> (t, d) . \<not> t \<le> wm'') buf"])
      apply (drule meta_spec[of _ "0"])
      apply (drule meta_mp)
       apply simp
       apply (meson LConsData insertI1)
      apply (drule meta_mp)
      using strict_monotone_drop_head apply blast
      apply simp
      done
    subgoal
      by (metis skip_n_productions_op_0 strict_monotone_drop_head)
    done
  subgoal for h x xs lxs' lgc' buf n
    apply (auto split: if_splits event.splits)
    apply (subgoal_tac "n = 0")
     defer
     apply (metis (mono_tags, lifting) One_nat_def diff_Suc_1 drop_eq_Nil2 le_eq_less_or_eq length_Cons length_drop less_2_cases list.size(3) not_less_iff_gr_or_eq numeral_2_eq_2)
    apply auto
    done
  done


lemma produce_skip_n_productions_op_does_not_produce_out_of_the_blue:
  "produce (skip_n_productions_op (sync_op buf) n) lxs = LCons (Data wm batch) lxs' \<Longrightarrow>
   \<not> (t \<in> ts lxs wm \<or> t \<in> fst ` set buf) \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   t \<notin> fst ` set batch"
  apply (subst (asm) produce.code)
  apply (auto split: option.splits)
  apply (metis (no_types, lifting) dual_order.refl fst_conv image_eqI produce_inner_Some_produce produce_inner_inner_skip_n_productions_sync_op_batch_le produce_inner_skip_n_productions_op_Some_Data_Watermark_in produce_inner_skip_n_productions_op_sync_op_xs produce_skip_n_productions_op_sync_op_in_ts_or_buf)
  done

lemma produce_inner_no_timestamps_out_of_the_blue:
  "produce_inner (skip_n_productions_op (sync_op buf) n, lxs) = Some (op, x, xs, lxs') \<Longrightarrow>
   x = Data wm batch \<Longrightarrow>
   xs = [Watermark wm] \<Longrightarrow>
   t \<notin> fst ` set buf \<Longrightarrow>
   \<not> (\<exists> d . Data t d \<in> lset lxs) \<Longrightarrow>
   t \<notin> fst ` set batch"
  apply (induct "(skip_n_productions_op (sync_op buf) n, lxs)" "(op, x, xs, lxs')" arbitrary: lxs lxs' op buf x xs n   rule: produce_inner_alt[consumes 1])
  subgoal for h lxs' lgc' lxs'a op buf x xs n
    apply (auto split: if_splits event.splits)
    using image_iff apply fastforce 
    using image_iff apply fastforce
      apply (smt (verit, ccfv_threshold) Un_iff append.right_neutral fst_conv image_iff set_ConsD set_append skip_n_productions_op_0)
     apply (smt (verit, best) fst_conv image_iff mem_Collect_eq set_filter skip_n_productions_op_0)
    apply (metis fst_conv imageI skip_n_productions_op_0)
    done
  subgoal for h x xs lxs' lgc' buf n
    apply hypsubst_thin
    apply (auto split: if_splits event.splits)
    apply (subgoal_tac "n = 0")
     defer
     apply (metis drop_Cons' drop_Nil list.discI)
    apply auto
    apply (metis fst_conv imageI)
    done
  done

lemma produce_no_timestamps_out_of_the_blue_aux:
  "produce (skip_n_productions_op (sync_op buf) n) lxs = LCons (Data wm batch) lxs' \<Longrightarrow>
   t \<notin> fst ` set buf \<Longrightarrow>
   \<not> (\<exists> d . Data t d \<in> lset lxs) \<Longrightarrow>
   t \<notin> fst ` set batch"
  apply (subst (asm) produce.code)
  apply (auto split: option.splits)
  apply (metis (no_types, lifting) fst_eqD produce_inner_no_timestamps_out_of_the_blue produce_inner_skip_n_productions_op_sync_op_xs rev_image_eqI)
  done

lemma produce_no_timestamps_out_of_the_blue:
  "x \<in> lset lxs' \<Longrightarrow>
   lxs' = produce (skip_n_productions_op (sync_op buf) n) lxs \<Longrightarrow>
   x = Data wm batch \<Longrightarrow>
   t \<notin> fst ` set buf \<Longrightarrow>
   \<not> (\<exists> d . Data t d \<in> lset lxs) \<Longrightarrow>
   t \<notin> fst ` set batch"
  apply (induct lxs' arbitrary: n rule: lset_induct)
   apply (metis produce_no_timestamps_out_of_the_blue_aux)
  apply (metis produce_skip_n_productions_op_LCons)
  done

lemma produce_inner_skip_n_productions_op_timestamp_not_produced_again_later_aux:
  "produce_inner (skip_n_productions_op (sync_op buf) n, lxs) = Some (op, x, xs, lxs') \<Longrightarrow>
   x = Data wm batch \<Longrightarrow>
   xs = [Watermark wm] \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   t \<in> fst ` set batch \<Longrightarrow>
   m > n \<Longrightarrow>
   produce_inner (skip_n_productions_op (sync_op buf) m, lxs) = Some (lgc', x', xs', lxs'') \<Longrightarrow>
   x' = Data wm' batch' \<Longrightarrow>
   xs' = [Watermark wm'] \<Longrightarrow>
   t \<notin> fst ` set batch'"
  apply (induct "(skip_n_productions_op (sync_op buf) n, lxs)" "(op, x, xs, lxs')" arbitrary: lxs lxs' op buf x xs n m rule: produce_inner_alt[consumes 1])
  subgoal for h lxs' lgc'a lxs'a op buf x xs n m
    apply (simp split: event.splits if_splits option.splits)
    subgoal for t d
      apply auto
      apply hypsubst_thin
      apply (drule meta_spec[of _ "buf @ [(t, d)]"])
      apply (drule meta_spec[of _ "n"])
      apply (drule meta_spec[of _ "m"])
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
      using strict_monotone_drop_head apply blast
      apply (subst (asm) produce_inner.simps)
      apply auto
      apply force
      done
    subgoal for t d
      apply auto
      apply hypsubst_thin
      apply (drule meta_spec[of _ "buf @ [(t, d)]"])
      apply (drule meta_spec[of _ "0"])
      apply (drule meta_spec[of _ "m"])
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
      using strict_monotone_drop_head apply blast
      apply (drule meta_mp)
       apply (subst (asm) produce_inner.simps)
       apply auto
      apply (subst (asm) produce_inner.simps)
      apply auto
      apply force
      done
    subgoal for wm
      apply hypsubst_thin
      apply (drule meta_spec[of _ "filter (\<lambda>(t, _). \<not> t \<le> wm) buf"])
      apply (drule meta_spec[of _ "n - Suc (Suc 0)"])
      apply (drule meta_spec[of _ "m - Suc (Suc 0)"])
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
      using strict_monotone_drop_head apply blast
      apply (drule meta_mp)
       apply (subst (asm) produce_inner.simps)
       apply auto
      apply (subst (asm) produce_inner.simps)
      apply (auto split: if_splits)
      apply (metis fst_conv image_iff)
      done
    subgoal for wm
      apply hypsubst_thin
      apply (drule meta_spec[of _ "buf"])
      apply (drule meta_spec[of _ "n"])
      apply (drule meta_spec[of _ "m"])
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
      using strict_monotone_drop_head apply blast
      apply (drule meta_mp)
       apply (subst (asm) produce_inner.simps)
       apply auto 
      apply (subst (asm) produce_inner.simps)
      apply auto
      apply force
      done
    subgoal for wm
      apply hypsubst_thin
      apply (drule meta_spec[of _ "filter (\<lambda>(t, _). \<not> t \<le> wm) buf"])
      apply (drule meta_spec[of _ "0"])
      apply (drule meta_spec[of _ "m - Suc (Suc 0)"])
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
      using strict_monotone_drop_head apply blast
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
       apply (subst (asm) produce_inner.simps)
       apply auto
      done   
    subgoal for wm
      apply hypsubst_thin
      apply (drule meta_spec[of _ "buf"])
      apply (drule meta_spec[of _ "0"])
      apply (drule meta_spec[of _ "m"])
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
      using strict_monotone_drop_head apply blast
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
       apply (subst (asm) produce_inner.simps)
       apply auto
      done
    done
  subgoal for h x xs lxs' lgc'a buf n m
    apply hypsubst_thin
    apply (auto split: if_splits event.splits list.splits)
    apply (subgoal_tac "n = 0")
     defer
     apply (metis drop_Cons' drop_Nil list.discI)
    apply auto
    apply (subst (asm) produce_inner.simps)
    apply (auto split: if_splits event.splits list.splits)
      apply hypsubst_thin
    subgoal
      using produce_inner_no_timestamps_out_of_the_blue[where wm=wm' and n="m - Suc (Suc 0)" and batch=batch' and
          buf="filter (\<lambda>(t, _). \<not> t \<le> wm) buf" and lxs=lxs' and op=lgc' and lxs'=lxs'' and t=t] apply simp
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
       apply (simp add: image_iff)
      apply (drule meta_mp)
       apply (meson Data_tail_ahead_of_t)
      apply force
      done
    subgoal
      using produce_inner_no_timestamps_out_of_the_blue[where wm=wm' and n="0" and batch=batch' and
          buf="filter (\<lambda>(t, _). \<not> t \<le> wm) buf" and lxs=lxs' and op=lgc' and lxs'=lxs'' and t=t] apply simp
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
       apply (simp add: image_iff)
      apply (drule meta_mp)
       apply (meson Data_tail_ahead_of_t)
      apply force
      done
    apply (metis (mono_tags, lifting) One_nat_def Suc_lessI diff_Suc_1 drop_eq_Nil2 le_eq_less_or_eq length_Cons length_drop list.size(3))
    done
  done

lemma produce_inner_skip_n_productions_op_timestamp_not_produced_again_later:
  "produce_inner (skip_n_productions_op (sync_op buf) n, lxs) = Some (op, x, xs, lxs') \<Longrightarrow>
   x = Data wm batch \<Longrightarrow>
   xs = [Watermark wm] \<Longrightarrow>
   t \<in> fst ` set batch \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   n' < n \<Longrightarrow>
   produce_inner (skip_n_productions_op (sync_op buf) n', lxs) = Some (lgc', x', xs', lxs'') \<Longrightarrow>
   x' = Data wm' batch' \<Longrightarrow>
   t \<notin> fst ` set batch'"
  apply (metis produce_inner_skip_n_productions_op_sync_op_xs produce_inner_skip_n_productions_op_timestamp_not_produced_again_later_aux)
  done

lemma produce_inner_sync_op_batch_le:
  "produce_inner (sync_op buf, lxs) = Some (op, x, xs, lxs') \<Longrightarrow>
   x = Data wm batch \<Longrightarrow>
   xs = [Watermark wm] \<Longrightarrow>
  (t, b) \<in> set batch \<Longrightarrow>
   t \<le> wm"
  apply (induct "(sync_op buf, lxs)" "(op, x, xs, lxs')" arbitrary: lxs lxs' op buf x xs rule: produce_inner_alt[consumes 1])
  subgoal 
    apply (auto split: event.splits if_splits)
    done
  subgoal for h x xs lxs' lgc' buf
    apply (auto split: event.splits if_splits)
    done
  done


lemma produce_inner_skip_n_productions_op_sync_op_coll_list_filter_Nil:
  "produce_inner (skip_n_productions_op (sync_op buf) n, LCons (Watermark wm) lxs) = Some (op, x, xs, lxs') \<Longrightarrow>
   x = Data wm' batch \<Longrightarrow>
   xs = [Watermark wm'] \<Longrightarrow>
   t \<in> fst ` set batch \<Longrightarrow>
   monotone (LCons (Watermark wm) lxs) WM \<Longrightarrow>
   \<exists>x\<in>set buf. (case x of (t, d) \<Rightarrow> t \<le> wm) \<Longrightarrow>
   Suc (Suc 0) \<le> n \<Longrightarrow>
   coll_list (filter (\<lambda>(t, d). t \<le> wm) buf) t = []"
  using produce_inner_skip_n_productions_op_timestamp_not_produced_again_later[where n'=0 and n=n and lxs="LCons (Watermark wm) lxs" and t=t] apply -
  apply (drule meta_spec)+
  apply (drule meta_mp)
   apply assumption
  apply (drule meta_mp)
   apply assumption
  apply (drule meta_mp)
   apply assumption
  apply (drule meta_mp)
   apply force
  apply (drule meta_mp)
   apply assumption
  apply (drule meta_mp)
   apply simp
  apply (drule meta_mp)
   apply (subst (asm) produce_inner.simps)
   apply (subst produce_inner.simps)
   apply (auto split:)
  apply (drule meta_mp)
   apply (intro conjI)
    apply (rule refl)+
  unfolding coll_list_def
  apply auto
  apply (smt (verit, ccfv_threshold) filter_False imageI mem_Collect_eq)
  done

subsection \<open>Soundness proofs\<close> 
lemma produce_inner_skip_n_productions_op_coll_soundness:
  "produce_inner (skip_n_productions_op (sync_op buf) n, lxs) = Some (op, x, xs, lxs') \<Longrightarrow>
   x = Data wm batch \<Longrightarrow>
   xs = [Watermark wm] \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   t \<in> fst ` set batch \<Longrightarrow>
   t \<le> wm \<Longrightarrow>
   coll lxs t + mset (coll_list buf t) = mset (coll_list batch t)"
  subgoal premises prems
    using prems apply -
    apply (induct "(skip_n_productions_op (sync_op buf) n, lxs)" "(op, x, xs, lxs')" arbitrary: lxs lxs' op buf x xs n rule: produce_inner_alt)
    using prems apply simp
    subgoal for h lxs' lgc' lxs'a op buf x xs n
      apply (auto split: if_splits event.splits)
      subgoal for t' d b
        apply (subst coll_LCons_coll_List[where WM=WM])
          apply (metis event.distinct(1) insertE llist.simps(19) produce_inner_skip_n_productions_op_Some_Data_Watermark_in)
        using strict_monotone_drop_head apply blast
        apply (drule meta_spec)+
        apply (drule meta_mp)
         apply (rule refl)
        apply (drule meta_mp)
        subgoal
          apply (subst (asm) produce_inner.simps)
          apply auto
          done
        apply (drule meta_mp)
        using strict_monotone_drop_head apply blast
        apply hypsubst_thin
        apply (drule sym)
        apply simp
        apply (simp add: add.commute add.left_commute)
        done
      subgoal for wm' d t'' b
        apply hypsubst_thin
        apply (drule meta_spec)+
        apply (drule meta_mp)
         apply (rule refl)
        apply (drule meta_mp)
        subgoal
          apply (subst (asm) produce_inner.simps)
          apply (auto split: if_splits)
          done
        apply (drule meta_mp)
        using strict_monotone_drop_head apply blast
        apply (subst (asm) produce_inner.simps)
        apply (auto split: if_splits)
        apply (drule produce_inner_skip_n_productions_op_sync_op_t_NOT_LE_Watermark[where t=t and WM=WM])
            apply (rule refl)+
          apply force
        using LConsWatermark apply blast
        apply (drule sym)
        apply auto
        unfolding coll_list_def
        apply auto
        apply (metis case_prod_unfold)
        done
      subgoal for wm' b
        apply hypsubst_thin
        apply (drule meta_spec)+
        apply (drule meta_mp)
         apply (rule refl)
        apply (drule meta_mp)
        subgoal
          apply (subst (asm) produce_inner.simps)
          apply (auto split: if_splits)
          done
        apply (drule meta_mp)
        using strict_monotone_drop_head apply blast
        apply simp
        done
      subgoal for t' d b
        apply hypsubst_thin
        apply (subst coll_LCons_coll_List[where WM=WM])
          apply (metis event.distinct(1) insertE llist.simps(19) produce_inner_sync_op_Watermark_in)
        using strict_monotone_drop_head apply blast
        apply (drule meta_spec)
        apply (drule meta_spec[of _ 0])
        apply (drule meta_mp)
         apply simp
        apply (drule meta_mp)
        subgoal
          apply (subst (asm) produce_inner.simps)
          apply (auto split: if_splits)
          done
        apply (drule meta_mp)
        using strict_monotone_drop_head apply blast
        apply simp
        apply (simp add: add.commute add.left_commute)
        done
      subgoal for wm' t' d b
        apply hypsubst_thin
        apply (drule meta_spec)
        apply (drule meta_spec[of _ 0])
        apply (drule meta_mp)
         apply simp
        apply (drule meta_mp)
        subgoal
          apply (subst (asm) produce_inner.simps)
          apply (auto split: if_splits)
          done
        apply (drule meta_mp)
        using strict_monotone_drop_head apply blast
        apply (subst (asm) produce_inner.simps)
        apply (auto split: if_splits)
        using produce_inner_skip_n_productions_op_sync_op_t_NOT_LE_Watermark[where t=t and x="Data wm batch" and WM=WM and n=0 and wm=wm and batch=batch and xs="[Watermark wm]"] apply simp
        apply (drule meta_spec)+
        apply (drule meta_mp)
         apply assumption+
        apply (drule meta_mp)
         apply force
        apply (drule meta_mp)
        using LConsWatermark apply blast
        apply (drule sym)
        unfolding coll_list_def
        apply auto
        apply (smt (verit) case_prod_unfold filter_mset_cong)
        done
      subgoal
        apply hypsubst_thin
        apply (drule meta_spec)
        apply (drule meta_spec[of _ 0])
        apply (drule meta_mp)
         apply simp
        apply (drule meta_mp)
        subgoal
          apply (subst (asm) produce_inner.simps)
          apply (auto split: if_splits)
          done
        apply (drule meta_mp)
        using strict_monotone_drop_head apply blast
        apply simp
        done
      done
    subgoal for h x xs lxs' lgc' buf n
      apply (auto split: if_splits event.splits)
      apply (subgoal_tac "n = 0")
       defer
       apply (metis drop_Cons' drop_Nil list.discI)
      apply hypsubst_thin
      apply auto
      apply (subst coll_empty)
       apply (meson Data_tail_ahead_of_t)
      unfolding coll_list_def
      apply auto
      apply (metis case_prod_unfold)
      done
    done
  done

lemma produce_skip_n_productions_op_sync_op_coll_soundness:
  "produce (skip_n_productions_op (sync_op buf) n) lxs = LCons (Data wm batch) lxs' \<Longrightarrow>
   t' \<in> fst ` set batch \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   coll lxs t' + mset (coll_list buf t') = mset (coll_list batch t')"
  apply (subst (asm) produce.code)
  apply (auto split: option.splits)
  apply (rule produce_inner_skip_n_productions_op_coll_soundness[where WM=WM])
       apply assumption+
      apply (rule refl)
     apply (simp add: produce_inner_skip_n_productions_op_sync_op_xs)
    apply assumption+
   apply force
  apply (frule produce_inner_inner_skip_n_productions_sync_op_batch_le[where t=t'])
     apply (rule refl)
    apply (simp add: produce_inner_skip_n_productions_op_sync_op_xs)
   apply force
  apply simp
  done

(* FIXME: Remove productive *)
lemma produce_skip_n_productions_op_sync_op_sync_op_soundness_LCons:
  "produce (skip_n_productions_op (sync_op buf) n) input_stream = LCons x output_stream \<Longrightarrow>
   monotone input_stream WM \<Longrightarrow>
   productive input_stream \<Longrightarrow>
   x = Data wm batch \<Longrightarrow>
   Watermark wm \<in> lset input_stream \<and>
   (\<forall> t \<in> fst ` set batch . t \<le> wm \<and> ((\<forall> t \<in> fst ` set buf . (\<forall> wm \<in> WM . \<not> t \<le> wm)) \<longrightarrow> (\<forall> wm \<in> WM . \<not> t \<le> wm))) \<and>
   batch \<noteq> [] \<and>
   (\<forall> (t, d) \<in> set batch .  Data t d \<in> lset input_stream \<or> (t, d) \<in> set buf)"
  apply (subst (asm) produce.corec.code)
  apply (simp split: option.splits)
  subgoal for out
    apply (cases out)
    subgoal premises prems for lgc' xa xs lxs'
      using prems(4,3,2,1,5,6) apply -
      apply hypsubst_thin
      apply (induction "(skip_n_productions_op (sync_op buf) n, input_stream)" "(lgc', xa, xs, lxs')" arbitrary: input_stream batch wm n buf rule: produce_inner_alt[consumes 1])
      subgoal for h lxs'a lgc'a n buf batch wm
        apply (simp split: llist.splits event.splits if_splits)
        subgoal premises prems2 for t d
          using prems2(1)[where batch=batch] prems2(2-) apply -
          apply hypsubst_thin
          apply (drule meta_spec)+
          apply (drule meta_mp)
           apply (rule refl)
          apply (drule meta_mp)
          using productive_drop_head apply blast
          apply (drule meta_mp)
          using strict_monotone_drop_head apply blast
          apply (drule meta_mp)
           apply simp
          apply (elim conjE)
          apply (intro conjI)
             apply blast
            apply (metis (mono_tags, lifting) LConsData Un_iff append.right_neutral fst_conv set_ConsD set_append)
           apply blast
          apply auto
          done
        subgoal premises prems2 for t d
          using prems2(1)[where batch=batch and buf="buf @ [(t, d)]" and n=0] prems2(2-) apply -
          apply hypsubst_thin
          apply (drule meta_mp)
           apply simp
          apply (drule meta_mp)
          using productive_drop_head apply blast
          apply (drule meta_mp)
          using strict_monotone_drop_head apply blast
          apply (drule meta_mp)
           apply simp
          apply (elim conjE)
          subgoal
            apply safe
               apply (cases " \<forall>x\<in>ws lxs'a wm. \<not> t \<le> x")
            subgoal 
              apply (cases "t \<le> wm")
              subgoal
                apply fastforce
                done
              subgoal
                by fastforce
              done
            subgoal
              by (smt (verit, del_insts) add_mset_add_single case_prod_conv dual_order.refl filter_mset_add_mset mset.simps(1) mset.simps(2) mset_append order_less_imp_le ws_correct)
              apply (smt (verit, best) LConsData Un_iff cons_append fst_conv set_ConsD set_append)
             apply force
            apply auto
            done
          done
        subgoal premises prems2 for wm'
          using prems2(2)[where batch=batch and buf="filter (\<lambda>(t, _). \<not> t \<le> wm') buf" and n="n - Suc (Suc 0)"] prems2(1,3-) apply -
          apply hypsubst_thin
          apply (drule meta_mp)
           apply simp
          apply (drule meta_mp)
          using productive_drop_head apply blast
          apply (drule meta_mp)
          using strict_monotone_drop_head apply blast
          apply (drule meta_mp)
           apply simp
          apply (elim conjE)
          apply fastforce
          done
        subgoal premises prems2 for wm'
          using prems2(2)[where batch=batch and buf="buf" and n="n"] prems2(1,3-) apply -
          apply hypsubst_thin
          apply (drule meta_mp)
           apply simp
          apply (drule meta_mp)
          using productive_drop_head apply blast
          apply (drule meta_mp)
          using strict_monotone_drop_head apply blast
          apply (drule meta_mp)
           apply simp
          apply (elim conjE)
          apply (auto simp add: ts_Watermark_in)
          done
        subgoal premises prems2 for wm'
          using prems2(1)[where batch=batch and buf="filter (\<lambda>(t, _). \<not> t \<le> wm') buf" and n="0"] prems2(2-) apply -
          apply hypsubst_thin
          apply (drule meta_mp)
           apply simp
          apply (drule meta_mp)
          using productive_drop_head apply blast
          apply (drule meta_mp)
          using strict_monotone_drop_head apply blast
          apply (drule meta_mp)
           apply simp
          apply (elim conjE)
          apply (auto simp add: ts_Watermark_in)
          apply (metis (mono_tags, opaque_lifting) fst_conv)
          done
        subgoal premises prems2 for wm'
          using prems2(1)[where batch=batch and buf="buf" and n="0"] prems2(2-) apply -
          apply hypsubst_thin
          apply (drule meta_mp)
           apply simp
          apply (drule meta_mp)
          using productive_drop_head apply blast
          apply (drule meta_mp)
          using strict_monotone_drop_head apply blast
          apply (drule meta_mp)
           apply simp
          apply (elim conjE)
          apply (auto simp add: ts_Watermark_in)
          done
        done
      subgoal for h n buf batch wm
        apply (simp split: llist.splits event.splits if_splits)
        apply (subgoal_tac "n = 0 \<or> n = 1")
         defer
         apply (metis One_nat_def Suc_lessI bot_nat_0.not_eq_extremum drop0 drop_Suc list.sel(3) list.simps(3))
        apply (elim disjE)
        subgoal for wm'
          apply simp
          apply (elim conjE)
          apply hypsubst_thin
          apply (auto simp add: ts_Watermark_in)
          apply (metis case_prodI filter_neq_nil_iff)     
          done
        subgoal for wm'
          apply simp
          done
        done
      done
    done
  done

(* FIXME: Remove productive *)
lemma produce_sync_op_soundness_aux:
  "x \<in> lset (produce (skip_n_productions_op (sync_op buf) n) lxs) \<Longrightarrow>
   x = Data wm batch \<Longrightarrow> 
   monotone lxs WM \<Longrightarrow>
   productive lxs \<Longrightarrow>
   (\<forall> t \<in> fst ` set batch . t \<le> wm \<and> ((\<forall> t \<in> fst ` set buf . (\<forall> wm \<in> WM . \<not> t \<le> wm)) \<longrightarrow> (\<forall> wm \<in> WM . \<not> t \<le> wm))) \<and>
   batch \<noteq> [] \<and>
   (\<forall> (t, d) \<in> set batch .  Data t d \<in> lset lxs \<or> (t, d) \<in> set buf)"
  apply (induct "produce (skip_n_productions_op (sync_op buf) n) lxs" arbitrary: wm batch n rule: llist.set_induct)
  subgoal for z1 z2 n wm batch
    using produce_skip_n_productions_op_sync_op_sync_op_soundness_LCons[where buf="buf" and x=z1 and input_stream=lxs and batch=batch and wm=wm and output_stream=z2 and n=n and WM=WM] apply auto
    done
  apply hypsubst
  subgoal for z1 z2 xa n wm batch
    apply (drule HOL.sym[where s="LCons z1 z2"])
    apply (cases z1)
    subgoal premises p for x11 x12
      apply (rule p(2)[where n="Suc n"])
         apply (subst produce_skip_n_productions_op_LCons[symmetric])
      using p(5) apply -
          apply assumption
      using p apply simp_all
      done
    subgoal premises p for x2
      apply (rule p(2)[where n="Suc n"])
         apply (subst produce_skip_n_productions_op_LCons[symmetric])
      using p(5) apply -
          apply assumption
      using p apply simp_all
      done
    done
  done

(* FIXME: Remove productive *)
lemma produce_sync_op_soundness:
  "Data wm batch \<in> lset (produce (sync_op buf) lxs) \<Longrightarrow>
   monotone lxs WM \<Longrightarrow> 
   productive lxs \<Longrightarrow>
   (\<forall> t \<in> fst ` set batch . t \<le> wm \<and> ((\<forall> t' \<in> fst ` set buf . (\<forall> wm \<in> WM . \<not> t' \<le> wm)) \<longrightarrow> (\<forall> wm \<in> WM . \<not> t \<le> wm))) \<and>
   batch \<noteq> [] \<and>
   (\<forall> (t, d) \<in> set batch .  Data t d \<in> lset lxs \<or> (t, d) \<in> set buf)"
  using produce_sync_op_soundness_aux[where n=0 and lxs=lxs and wm=wm and batch=batch] apply auto
  done

lemma produce_sync_op_soundness_alt:
  "Data wm batch \<in> lset (produce (sync_op buf) lxs) \<Longrightarrow>
   monotone lxs WM \<Longrightarrow> 
   productive lxs \<Longrightarrow>
   (\<forall> t' \<in> fst ` set buf . (\<forall> wm \<in> WM . \<not> t' \<le> wm)) \<longrightarrow> (\<forall> t \<in> fst ` set batch . (\<forall> wm \<in> WM . \<not> t \<le> wm)) \<and>
   batch \<noteq> [] \<and>
   (\<forall> (t, d) \<in> set batch .  Data t d \<in> lset lxs \<or> (t, d) \<in> set buf)"
  by (simp add: produce_sync_op_soundness)

(* FIXME: Remove productive *)
lemma produce_skip_n_productions_op_sync_op_sync_op_soundness_LCons_stronger:
  "produce (skip_n_productions_op (sync_op buf) n) input_stream = LCons x output_stream \<Longrightarrow>
   monotone input_stream WM \<Longrightarrow>
   productive input_stream \<Longrightarrow>
   x = Data wm batch \<Longrightarrow>
   (\<forall>t\<in>set (map fst batch). coll input_stream t + (mset (map snd (filter (\<lambda>(t', d). t' = t) buf))) = mset (map snd (filter (\<lambda>(t', d). t' = t) batch))) \<and>
   sync_ts input_stream wm \<union> {t \<in> fst ` set buf . t \<le> wm \<and> \<not> (\<exists> wm' \<in> ws input_stream wm . t \<le> wm')} = set (map fst batch) \<and>
   Watermark wm \<in> lset input_stream"
  apply (subst (asm) produce.corec.code)
  apply (simp split: option.splits)
  subgoal for out
    apply (cases out)
    subgoal premises prems for lgc' xa xs lxs'
      using prems(4,3,2,1,5,6) apply -
      apply hypsubst_thin
      apply (induction "(skip_n_productions_op (sync_op buf) n, input_stream)" "(lgc', xa, xs, lxs')" arbitrary: input_stream batch wm n buf rule: produce_inner_alt[consumes 1])
      subgoal for h lxs'a lgc'a n buf batch wm
        apply (simp split: llist.splits event.splits if_splits)
        subgoal premises prems2 for t d
          using prems2(1)[where batch="batch"] prems2(2-) apply -
          apply hypsubst_thin
          apply (drule meta_spec)+
          apply (drule meta_mp)
           apply (rule refl)
          apply (drule meta_mp)
          using productive_drop_head apply blast
          apply (drule meta_mp)
          using strict_monotone_drop_head apply blast
          apply (drule meta_mp)
           apply simp
          apply (elim conjE)
          apply (rule conjI)
          subgoal
            apply (smt (verit, ccfv_threshold) add.assoc add.commute add_mset_add_single case_prod_unfold coll_diff_head_2 coll_eq_coll_ltl filter_mset_add_mset fst_conv image_mset_single image_mset_union mset.simps(1) mset.simps(2) mset_append prod.sel(2) productive_drop_head strict_monotone_drop_head)
            done
          subgoal
            apply (rule conjI)
            subgoal
              apply (drule sym)
              apply (simp only: )
              apply (cases "t \<le> wm")
              subgoal
                apply (cases "t \<in> ws lxs'a wm")
                unfolding sync_ts_def
                 apply auto
                done
              subgoal
                unfolding sync_ts_def
                apply auto
                done
              done
            subgoal
              apply blast
              done
            done
          done
        subgoal premises prems2 for t d
          using prems2(1)[where batch="batch" and n=0] prems2(2-) apply -
          apply hypsubst_thin
          apply (drule meta_spec)+
          apply (drule meta_mp)
           apply simp
          apply (drule meta_mp)
          using productive_drop_head apply blast
          apply (drule meta_mp)
          using strict_monotone_drop_head apply blast
          apply (drule meta_mp)
           apply simp
          apply (elim conjE)
          apply (rule conjI)
          subgoal
            apply (smt (verit, ccfv_threshold) add.assoc add.commute add_mset_add_single case_prod_unfold coll_diff_head_2 coll_eq_coll_ltl filter_mset_add_mset fst_conv image_mset_single image_mset_union mset.simps(1) mset.simps(2) mset_append prod.sel(2) productive_drop_head strict_monotone_drop_head)
            done
          subgoal
            apply (rule conjI)
            subgoal
              apply (drule sym)
              apply (simp only: )
              apply (cases "t \<le> wm")
              subgoal
                apply (cases "t \<in> ws lxs'a wm")
                subgoal
                  unfolding sync_ts_def
                  apply auto
                  done
                subgoal
                  unfolding sync_ts_def
                  apply auto
                  done
                done
              subgoal
                unfolding sync_ts_def
                apply auto
                done
              done
            subgoal
              apply blast
              done
            done
          done
        subgoal premises prems2 for wm'
          using prems2(2)[where batch="batch" and n="n - Suc (Suc 0)"] prems2(1,3-) apply -
          apply hypsubst_thin
          apply (drule meta_spec)+
          apply (drule meta_mp)
           apply simp
          apply (drule meta_mp)
          using productive_drop_head apply blast
          apply (drule meta_mp)
          using strict_monotone_drop_head apply blast
          apply (drule meta_mp)
           apply simp
          apply (cases "wm \<le> wm'")
           apply (cases "Watermark wm \<in> lset lxs'a")
          subgoal
            apply simp
            apply (elim conjE)
            apply (meson tail_incomparable)
            done
          subgoal
            apply simp
            done
          subgoal
            apply simp
            apply (elim conjE)
            apply (subgoal_tac "\<forall> t \<in> fst ` set batch . \<not> t \<le> wm'")
             defer
            subgoal
              apply (drule sym)
              apply simp
              apply (subst ball_Un)
              apply (rule conjI)
              unfolding sync_ts_def
               apply (metis (no_types, lifting) dual_order.refl mem_Collect_eq ts_all_not_le)
              apply (simp add: image_iff)
              done
            apply (rule conjI)
            subgoal
              apply (smt (verit, ccfv_threshold) case_prod_unfold filter_mset_cong image_eqI)
              done
            subgoal
              unfolding sync_ts_def
              apply simp
              apply (drule sym)
              apply simp
              apply safe
                           apply (simp_all add: image_iff ts_Watermark_in)
                    apply (meson dual_order.refl ts_all_not_le)+
                 apply (simp add: image_iff)
                 apply force+
              done
            done
          done
        subgoal premises prems2 for wm'
          using prems2(2)[where batch="batch" and n="n"] prems2(1,3-) apply -
          apply hypsubst_thin
          apply (drule meta_spec)+
          apply (drule meta_mp)
           apply simp
          apply (drule meta_mp)
          using productive_drop_head apply blast
          apply (drule meta_mp)
          using strict_monotone_drop_head apply blast
          apply (drule meta_mp)
           apply simp
          apply (cases "wm \<le> wm'")
          subgoal
            apply (cases "Watermark wm \<in> lset lxs'a")
            subgoal
              apply (meson tail_incomparable)
              done
            subgoal
              apply force
              done
            done
          subgoal
            apply simp
            apply (elim conjE)
            apply (subgoal_tac "\<forall> t \<in> fst ` set batch . \<not> t \<le> wm'")
             defer
            subgoal
              apply (drule sym)
              apply simp
              apply (subst ball_Un)
              apply (rule conjI)
              unfolding sync_ts_def
               apply (metis (no_types, lifting) dual_order.refl mem_Collect_eq ts_all_not_le)
              apply force
              done
            unfolding sync_ts_def
            apply simp
            apply (drule sym)
            apply (simp_all add: image_iff ts_Watermark_in)
            apply safe
                   apply blast
                  apply (meson dual_order.refl ts_all_not_le)+
               apply blast
              apply blast
             apply auto
            done
          done
        subgoal premises prems2 for wm'
          using prems2(1)[where batch="batch" and n="0"] prems2(2-) apply -
          apply hypsubst_thin
          apply (drule meta_spec)+
          apply (drule meta_mp)
           apply simp
          apply (drule meta_mp)
          using productive_drop_head apply blast
          apply (drule meta_mp)
          using strict_monotone_drop_head apply blast
          apply (drule meta_mp)
           apply simp
          apply (cases "wm \<le> wm'")
          subgoal
            apply (cases "Watermark wm \<in> lset lxs'a")
             apply (meson tail_incomparable)
            apply meson
            done
          subgoal
            apply simp
            apply (elim conjE)
            apply (subgoal_tac "\<forall> t \<in> fst ` set batch . \<not> t \<le> wm'")
             defer
            subgoal
              apply (drule sym)
              apply simp
              apply (subst ball_Un)
              apply (rule conjI)
              unfolding sync_ts_def
               apply (metis (no_types, lifting) dual_order.refl mem_Collect_eq ts_all_not_le)
              apply force
              done
            unfolding sync_ts_def
            apply simp
            apply (rule conjI)
             apply (smt (verit, ccfv_SIG) case_prod_unfold filter_cong mset_filter)
            apply (drule sym)
            apply (simp_all add: image_iff ts_Watermark_in)
            apply safe
                apply force
               apply (meson dual_order.refl ts_all_not_le)+
            apply force
            done
          done
        subgoal premises prems2 for wm'
          using prems2(1)[where batch="batch" and n="0"] prems2(2-) apply -
          apply hypsubst_thin
          apply (drule meta_spec)+
          apply (drule meta_mp)
           apply simp
          apply (drule meta_mp)
          using productive_drop_head apply blast
          apply (drule meta_mp)
          using strict_monotone_drop_head apply blast
          apply (drule meta_mp)
           apply simp
          apply (cases "wm \<le> wm'")
          subgoal
            apply (cases "Watermark wm \<in> lset lxs'a")
             apply (meson tail_incomparable)
            apply meson
            done
          subgoal
            apply simp
            subgoal
              apply simp
              apply (elim conjE)
              apply (subgoal_tac "\<forall> t \<in> fst ` set batch . \<not> t \<le> wm'")
               defer
              subgoal
                apply (drule sym)
                apply simp
                apply (subst ball_Un)
                apply (rule conjI)
                unfolding sync_ts_def
                 apply (metis (no_types, lifting) dual_order.refl mem_Collect_eq ts_all_not_le)
                apply force
                done
              unfolding sync_ts_def
              apply simp
              apply safe
                     apply (smt (verit, del_insts) UnI1 insert_iff mem_Collect_eq ts_Watermark_in)
                    apply (smt (verit, del_insts) UnCI image_eqI insert_iff mem_Collect_eq ts_Watermark_in)
                   apply fast
                  apply (smt (verit, best) Collect_disj_eq imageI insert_compr mem_Collect_eq ts_Watermark_in)+
              done
            done
          done
        done
      subgoal for h n buf batch wm
        apply (simp split: llist.splits event.splits if_splits)
        apply (subgoal_tac "n = 0 \<or> n = 1")
         defer
         apply (metis One_nat_def Suc_lessI bot_nat_0.not_eq_extremum drop0 drop_Suc list.sel(3) list.simps(3))
        apply (elim disjE)
        subgoal for wm'
          apply simp
          apply (elim conjE)
          apply hypsubst_thin
          apply simp
          apply (rule conjI)
           apply (smt (verit, best) add_cancel_right_left case_prod_unfold coll_eq_coll_ltl_Watermark dual_order.refl empty_def filter_mset_cong lset_intros(1) mem_Collect_eq not_finite_existsD not_in_ts_coll_empty ts_strict_monotone_eq_empty)
          unfolding sync_ts_def
          apply (subst ws_strict_monotone_LCons_empty[where WM=WM])
           apply simp
          apply simp
          apply (subst ts_strict_monotone_eq_empty_ltl[where WM=WM])
           apply simp
          apply simp
          apply safe
             apply (metis (mono_tags, lifting) case_prod_unfold image_eqI mem_Collect_eq)
            apply (metis (mono_tags, lifting) image_eqI)
           apply fastforce
          apply (simp add: ws_strict_monotone_empty ts_Watermark_in)
          done
        subgoal for wm'
          apply simp
          done
        done
      done
    done
  done


(* FIXME: Remove productive *)
lemma produce_sync_op_soundness_timestamps_aux:
  "x \<in> lset (produce (skip_n_productions_op (sync_op buf) n) lxs) \<Longrightarrow>
   x = Data wm batch \<Longrightarrow>
   monotone lxs WM \<Longrightarrow> 
   productive lxs \<Longrightarrow>
   sync_ts lxs wm \<union> {t \<in> fst ` set buf . t \<le> wm \<and> \<not> (\<exists> wm' \<in> ws lxs wm . t \<le> wm')} = set (map fst batch) \<and>
   (\<forall> t \<in> set (map fst batch) . coll lxs t + (mset (map snd (filter (\<lambda>(t', d). t' = t) buf))) = mset (map snd (filter (\<lambda> (t', d) . t' = t) batch)))"
  apply (induct "produce (skip_n_productions_op (sync_op buf) n) lxs" arbitrary: wm batch n rule: llist.set_induct)
  subgoal for z1 z2 n wm batch
    using produce_skip_n_productions_op_sync_op_sync_op_soundness_LCons_stronger[where buf=buf and x=z1 and input_stream=lxs and batch=batch and wm=wm and output_stream=z2 and n=n and WM=WM] apply auto
    done
  subgoal for z1 z2 xa n wm batch
    apply (drule HOL.sym[where s="LCons z1 z2"])
    apply (cases z1)
    subgoal premises p for x11 x12
      apply (rule p(2)[where n="Suc n"])
         apply (subst produce_skip_n_productions_op_LCons[symmetric])
      using p apply -
          apply assumption
      using p apply simp_all
      done
    subgoal premises p for x2
      apply (rule p(2)[where n="Suc n"])
         apply (subst produce_skip_n_productions_op_LCons[symmetric])
      using p apply -
          apply assumption
      using p apply simp_all
      done
    done
  done

(* FIXME: Remove productive *)
lemma produce_sync_op_soundness_timestamps:
  "Data wm batch \<in> lset (produce (sync_op buf) lxs) \<Longrightarrow>
   monotone lxs WM \<Longrightarrow> 
   productive lxs \<Longrightarrow>
   sync_ts lxs wm \<union> {t \<in> fst ` set buf . t \<le> wm \<and> \<not> (\<exists> wm' \<in> ws lxs wm . t \<le> wm')} = set (map fst batch) \<and>
   (\<forall> t \<in> set (map fst batch) . coll lxs t + (mset (map snd (filter (\<lambda>(t', d). t' = t) buf))) = mset (map snd (filter (\<lambda> (t', d) . t' = t) batch)))"
  using produce_sync_op_soundness_timestamps_aux[where n=0 and x="Data wm batch"] apply simp
  done

(* FIXME: Remove productive *)
lemma lnth_Data_produce_inner_Some_skip_n_productions_op_sync_op_LCons_batch_not_ge:
  "produce_inner (skip_n_productions_op (sync_op buf) m, lxs) = Some (lgc', x, xs, lxs') \<Longrightarrow>
   x = Watermark wm \<Longrightarrow>
   lnth (xs @@- produce lgc' lxs') n = Data t batch \<Longrightarrow>
   enat n < llength (xs @@- produce lgc' lxs') \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   productive lxs \<Longrightarrow>
   \<forall>t\<in>set batch. \<not> fst t \<le> wm"
  apply (induct "(skip_n_productions_op (sync_op buf) m, lxs)" "(lgc', x, xs, lxs')" arbitrary: n m buf lxs lxs' x xs t batch wm lgc' WM rule: produce_inner_alt[consumes 1])
  subgoal for h lxs' lgc' m buf lxs'a x xs lgc'a n t batch wm WM
    apply hypsubst_thin
    apply (auto split: if_splits event.splits)
         apply (metis (mono_tags) fst_conv productive_drop_head strict_monotone_drop_head)+
      apply (metis fst_conv productive_drop_head skip_n_productions_op_0 strict_monotone_drop_head)+
    done
  subgoal for h x xs lxs' lgc' m buf n t batch wm WM
    apply (simp add: split_beta split: if_splits prod.splits list.splits event.splits)
    apply (subgoal_tac "m = 1 \<or> m = 0")
     defer
     apply (metis One_nat_def Suc_lessI bot_nat_0.not_eq_extremum drop0 drop_Suc_Cons list.discI)
    apply (elim disjE)    
    subgoal for wm'
      apply hypsubst_thin
      apply (cases "length xs \<le> n")
      subgoal
        apply (subgoal_tac "\<forall>t\<in>sync_ts (LCons (Watermark wm') lxs') t \<union> {taa \<in> fst ` set buf. taa \<le> t \<and> (\<forall>x\<in>ws (LCons (Watermark wm') lxs') t. \<not> taa \<le> x)}. \<not> t \<le> wm")
         defer
        subgoal
          apply (simp add: sync_ts_def ts_Watermark_in image_iff split_beta split: if_splits prod.splits list.splits event.splits)
          apply (elim conjE)
          apply hypsubst_thin
          apply (rule conjI; rule impI)
          using tail_incomparable apply auto[1]
          apply (metis (no_types, lifting) ldropn_Suc_conv_ldropn produce_skip_n_productions_op_Some_Data_Watermark_in_LCons produce_skip_n_productions_op_correctness )
          done
        using produce_sync_op_soundness_timestamps_aux[unfolded in_lset_conv_lnth, OF exI, OF conjI, rotated 1,
            where n1="n - length xs" and x="Data t batch" and lxs=lxs' and wm=t and batch=batch and n=0 and WM="insert wm WM" and buf="filter (\<lambda>(t, _). \<not> t \<le> wm') buf"] apply -
        apply (drule meta_mp)
         apply (simp only: skip_n_productions_op_0)
         apply (metis (no_types, lifting) One_nat_def diff_zero drop0 drop_Suc_Cons list.size(3) lshift.simps(1))
        apply (drule meta_mp)
         apply (rule refl)
        apply (drule meta_mp)
         apply (metis One_nat_def drop0 drop_Suc_Cons event.inject(2) list.inject strict_monotone_LCons_Watermark_insert)
        apply (drule meta_mp)
        using productive_drop_head apply blast
        apply (drule meta_mp)
         apply (metis (no_types, lifting) One_nat_def diff_zero drop0 drop_Suc_Cons list.size(3) lshift.simps(1) skip_n_productions_op_0)
        subgoal premises prems
          using prems(9,10) apply (auto simp add: ts_Watermark_in image_iff  split_beta split: if_splits)
            apply (metis (no_types, lifting) One_nat_def drop0 drop_Suc_Cons ldropn_Suc_conv_ldropn prems(1) prems(3) prems(4) prems(5) produce_skip_n_productions_op_Some_Data_Watermark_in_LCons produce_skip_n_productions_op_correctness lshift.simps(1) tail_incomparable)
          subgoal
            unfolding sync_ts_def
            apply auto
            apply (smt (verit, ccfv_threshold) One_nat_def Un_iff drop0 drop_Suc_Cons dual_order.refl event.inject(2) fst_conv image_eqI list.inject mem_Collect_eq prems(1) prems(5) ts_Watermark_in ts_all_not_le)
            done
          apply (metis (no_types, lifting) One_nat_def drop0 drop_Suc_Cons ldropn_Suc_conv_ldropn prems(1) prems(3) prems(4) produce_skip_n_productions_op_Some_Data_Watermark_in_LCons produce_skip_n_productions_op_correctness lshift.simps(1))
          done
        done
      subgoal
        apply (metis One_nat_def drop0 drop_Suc_Cons leI list.size(3) not_less_zero)
        done
      done
    apply auto
    done
  done

(* FIXME: Remove productive *)
lemma lnth_Data_produce_skip_n_productions_op_sync_op_sync_op_soundness_LCons_batch_not_ge:
  "monotone lxs WM \<Longrightarrow>
   productive lxs \<Longrightarrow>
   lnth hs n = Data t batch \<Longrightarrow>
   enat (Suc n) \<le> llength hs \<Longrightarrow> produce (skip_n_productions_op (sync_op buf) i) lxs = LCons (Watermark wm) hs \<Longrightarrow> \<forall>t\<in>set batch. \<not> fst t \<le> wm"
  apply (subst (asm) produce.code)
  apply (auto split: option.splits split: prod.splits)
  using lnth_Data_produce_inner_Some_skip_n_productions_op_sync_op_LCons_batch_not_ge 
  apply (metis Suc_ile_eq fst_conv)
  done

(* FIXME: Remove productive *)
lemma lnth_produce_skip_n_productions_op_sync_op_batch_not_ge:
  "x = Data t batch \<Longrightarrow> 
   monotone lxs WM \<Longrightarrow>
   productive lxs \<Longrightarrow>
   lnth (produce (skip_n_productions_op (sync_op buf) i) lxs) n = x\<Longrightarrow>
   m < n \<Longrightarrow>
   lnth (produce (skip_n_productions_op (sync_op buf) i) lxs) m = Watermark wm  \<Longrightarrow>
   n < llength (produce (skip_n_productions_op (sync_op buf) i) lxs) \<Longrightarrow>
   (\<forall> t \<in> fst ` set batch .\<not> t \<le> wm)"
  apply (induct n arbitrary: i buf lxs WM t batch m )
   apply fast
  apply simp
  subgoal for n i buf lxs WM t batch m 
    apply (cases "produce (skip_n_productions_op (sync_op buf) i) lxs")
     apply simp
    subgoal for h hs
      apply simp
      apply (cases m)
       apply simp
      subgoal 
        apply hypsubst_thin
        using lnth_Data_produce_skip_n_productions_op_sync_op_sync_op_soundness_LCons_batch_not_ge apply blast 
        done
      apply simp
      apply (drule meta_spec[of _ "Suc i"])
      apply (drule meta_spec[of _ "buf"])
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
       apply assumption
      apply (drule meta_mp)
       apply assumption
      apply (drule meta_mp)
      subgoal for n'
        apply hypsubst_thin
        apply (subst (asm) produce_skip_n_productions_op_correctness)
        apply (subst produce_skip_n_productions_op_correctness)
        apply (subst lnth_ldropn)
         apply (smt (verit) Suc_ile_eq add.commute ldropn_Suc_conv_ldropn ldropn_eq_LConsD ldropn_ldropn llist.inject)
        apply (metis (mono_tags, lifting) Suc_ile_eq ldropn_Suc_conv_ldropn ldropn_eq_LConsD ldropn_ldropn llist.inject)
        done
      apply (drule meta_mp)
       apply assumption
      apply (drule meta_mp)
      subgoal for n'
        apply hypsubst_thin
        apply (subst (asm) produce_skip_n_productions_op_correctness)
        apply (subst produce_skip_n_productions_op_correctness)
        apply (subst lnth_ldropn)
         apply (smt (verit, ccfv_threshold) Suc_ile_eq add.commute enat_ord_simps(2) ldropn_Suc_conv_ldropn ldropn_eq_LConsD ldropn_ldropn order_less_subst2 produce_skip_n_productions_op_correctness produce_skip_n_productions_op_LCons)
        apply (smt (verit, ccfv_SIG) Suc_ile_eq enat_ord_simps(2) ldropn_Suc_conv_ldropn ldropn_eq_LConsD ldropn_ldropn llist.inject order_less_subst2)
        done
      apply (erule meta_mp)
      using Suc_ile_eq
      by (metis produce_skip_n_productions_op_LCons)
    done
  done

lemma produce_skip_n_productions_op_Suc_Suc_EX:
  "produce (skip_n_productions_op (sync_op (filter (\<lambda>(t, _). \<not> t \<le> wm) buf)) n) lxs' = LCons (Data wm' batch') lxs'' \<Longrightarrow>
   \<exists> (t, d) \<in> set buf . t \<le> wm \<Longrightarrow>
   \<exists>lxs''. produce (skip_n_productions_op (sync_op buf) (Suc (Suc n))) (LCons (Watermark wm) lxs') = LCons (Data wm' batch') lxs''"
  apply (subst produce_skip_n_productions_op_correctness)
  apply (subst (asm) produce_skip_n_productions_op_correctness)
  apply (subst in_buf_produce_Watermark)
   apply simp
  apply simp
  done

lemma produce_inner_skip_n_productions_op_sync_op_smaller:
  "produce_inner (skip_n_productions_op (sync_op buf) n, lxs) = Some (op, x, xs, lxs') \<Longrightarrow>
   x = Data wm batch \<Longrightarrow>
   xs = [Watermark wm] \<Longrightarrow>
   t \<le> wm \<Longrightarrow>
   t \<in> ts lxs wm \<or> t \<in> fst ` set buf \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   \<exists>n'\<le>n. \<exists>wm' batch'. (\<exists>lxs'. produce (skip_n_productions_op (sync_op buf) n') lxs = LCons (Data wm' batch') lxs') \<and> t \<in> fst ` set batch'"
  apply (induct "(skip_n_productions_op (sync_op buf) n, lxs)" "(op, x, xs, lxs')" arbitrary: lxs lxs' op buf x xs n rule: produce_inner_alt[consumes 1])
  subgoal for h lxs' lgc' lxs'a op buf x xs n
    apply (auto simp add: in_buf_produce_Watermark split: event.splits if_splits)
    subgoal
      by (simp add: produce_Data produce_skip_n_productions_op_correctness strict_monotone_drop_head)
    subgoal
      by (metis produce_Data produce_skip_n_productions_op_correctness strict_monotone_drop_head)
    subgoal
      by (smt (verit) Un_iff fst_conv imageI produce_Data produce_skip_n_productions_op_correctness set_append strict_monotone_drop_head)
    subgoal
      by (metis fst_conv imageI in_set_conv_decomp le_zero_eq produce_Data skip_n_productions_op_0 strict_monotone_drop_head)
    subgoal
      by (metis le_zero_eq produce_Data skip_n_productions_op_0 strict_monotone_drop_head)
    subgoal
      by (metis Orderings.order_eq_iff Un_iff bot_nat_0.extremum fst_conv imageI produce_Data set_append skip_n_productions_op_0 strict_monotone_drop_head)
    subgoal for t d
      apply hypsubst_thin
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
      using strict_monotone_drop_head apply blast
      apply (simp add: produce_Data produce_skip_n_productions_op_correctness)
      done
    subgoal
      by (smt (verit, ccfv_threshold) Un_iff fst_conv imageI produce_Data produce_skip_n_productions_op_correctness set_append strict_monotone_drop_head)
    subgoal
      apply (metis Un_iff bot_nat_0.extremum_unique fst_conv image_eqI in_ts_LCons_Data_cases list.set_intros(1) produce_Data set_append skip_n_productions_op_0 strict_monotone_drop_head)
      done
    subgoal for wm t d
      apply hypsubst_thin
      apply (drule meta_spec)
      apply (drule meta_spec[of _ 0])
      apply simp
      apply (drule meta_mp)
      using strict_monotone_drop_head apply blast
      apply (drule meta_mp)
       apply force
      apply (drule meta_mp)
      using strict_monotone_drop_head apply blast
      apply (simp add: produce_Data)
      done
    subgoal for wm t d
      apply hypsubst_thin
      apply (drule meta_spec[of _ "filter (\<lambda>(t, _). \<not> t \<le> wm) buf"])
      apply (drule meta_spec[of _ "n - Suc (Suc 0)"])
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
      using strict_monotone_drop_head apply blast
      apply (elim conjE exE)
      subgoal for n' wm' batch' lxs''
        apply (rule exI[of _ "Suc (Suc n')"])
        apply auto
        apply (rule exI[of _ wm'])
        apply (rule exI[of _ batch'])
        apply safe
        using produce_skip_n_productions_op_Suc_Suc_EX 
         apply blast
        apply force
        done
      done
    subgoal for wm' t' d d'
      apply hypsubst_thin
      apply (cases "wm \<le> wm'")
      subgoal
        apply (rule exI[of _ 0])
        apply simp
        apply (subst in_buf_produce_Watermark)
         apply fast
        apply simp
        apply (metis (no_types, lifting) case_prodI fst_conv image_iff mem_Collect_eq order_trans)
        done
      subgoal
        apply (cases "t \<le> t'")
        subgoal
          apply (rule exI[of _ 0])
          apply simp
          apply (subst in_buf_produce_Watermark)
           apply fast
          apply simp
          apply (metis (no_types, lifting) case_prodI fst_conv image_iff mem_Collect_eq order_trans)
          done
        subgoal
          apply (cases "t \<le> wm'")
          subgoal
            apply (rule exI[of _ 0])
            apply simp
            apply (subst in_buf_produce_Watermark)
             apply fast
            apply simp
            apply (metis (no_types, lifting) case_prodI fst_conv image_iff mem_Collect_eq)
            done  
          subgoal
            apply (drule meta_spec)+
            apply (drule meta_mp)
             apply (rule refl)
            apply (drule meta_mp)
            subgoal
              apply (rule disjI2)
              apply auto
              apply force
              done
            apply (drule meta_mp)
            using strict_monotone_drop_head apply blast
            apply (elim conjE exE)
            subgoal for n' wm'' batch' lxs'
              apply (rule exI[of _ "Suc (Suc n')"])
              apply auto
              apply (rule exI[of _ wm''])
              apply (rule exI[of _ batch'])
              apply safe
              using produce_skip_n_productions_op_Suc_Suc_EX 
               apply blast
              apply force
              done
            done
          done
        done
      done
    subgoal for wm
      apply hypsubst_thin
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
      using strict_monotone_drop_head apply blast
      apply (simp add: not_in_buf_produce_Watermark produce_Data produce_skip_n_productions_op_correctness)
      done
    subgoal for wm d
      apply hypsubst_thin
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
       apply force
      apply (drule meta_mp)
      using strict_monotone_drop_head apply blast
      apply (simp add: not_in_buf_produce_Watermark produce_Data produce_skip_n_productions_op_correctness)
      done
    subgoal for wm t d
      apply hypsubst_thin
      apply (drule meta_spec)
      apply (drule meta_spec[of _ 0])
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
      using strict_monotone_drop_head apply blast
      apply (simp add:  produce_Data produce_skip_n_productions_op_correctness)
      apply (subst in_buf_produce_Watermark)
       apply fast
      apply (rule exI[of _ 2])
      apply simp
      apply (simp add: numeral_2_eq_2)
      done
    subgoal for wm' t' d d'
      apply hypsubst_thin
      apply (cases "wm \<le> wm'")
      subgoal
        apply (rule exI[of _ 0])
        apply simp
        apply (subst in_buf_produce_Watermark)
         apply fast
        apply simp
        apply (metis (no_types, lifting) case_prodI fst_conv image_iff mem_Collect_eq order_trans)
        done
      subgoal
        apply (cases "t \<le> t'")
        subgoal
          apply (rule exI[of _ 0])
          apply simp
          apply (subst in_buf_produce_Watermark)
           apply fast
          apply simp
          apply (metis (no_types, lifting) case_prodI fst_conv image_iff mem_Collect_eq order_trans)
          done
        subgoal
          apply (cases "t \<le> wm'")
          subgoal
            apply (rule exI[of _ 0])
            apply simp
            apply (subst in_buf_produce_Watermark)
             apply fast
            apply simp
            apply (metis (no_types, lifting) case_prodI fst_conv image_iff mem_Collect_eq)
            done  
          subgoal
            apply (drule meta_spec)
            apply (drule meta_spec[of _ 0])
            apply (drule meta_mp)
             apply simp
            apply (drule meta_mp)
            subgoal
              apply (rule disjI2)
              apply auto
              apply force
              done
            apply (drule meta_mp)
            using strict_monotone_drop_head apply blast
            apply (elim conjE exE)
            subgoal for n' wm'' batch' lxs'
              apply (rule exI[of _ "Suc (Suc n')"])
              apply auto
              apply (rule exI[of _ wm''])
              apply (rule exI[of _ batch'])
              apply safe
               apply (metis case_prod_conv produce_skip_n_productions_op_Suc_Suc_EX skip_n_productions_op_0)
              apply force
              done
            done
          done
        done
      done
    subgoal
      by (metis bot_nat_0.extremum_unique not_in_buf_produce_Watermark skip_n_productions_op_0 strict_monotone_drop_head)
    subgoal
      apply (drule meta_spec)
      apply (drule meta_spec[of _ 0])
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
       apply force
      apply (metis bot_nat_0.extremum_uniqueI not_in_buf_produce_Watermark skip_n_productions_op_0 strict_monotone_drop_head)
      done
    done
  subgoal for h x xs lxs' lgc' buf n
    apply (auto simp add: in_buf_produce_Watermark split: event.splits if_splits)
     apply (subgoal_tac "n = 0")
      prefer 2
    subgoal 
      apply (metis drop_Cons' drop_Nil list.discI)
      done
    subgoal for x2 a b
      apply auto
      apply hypsubst_thin
      apply (subst produce.code)
      apply (simp split: option.splits)
      apply (subst (1 2) produce_inner.simps)
      apply (auto split: prod.splits)
      using in_ts_strict_monotone_False apply blast
      done
    subgoal for x2 a b ba
      apply (subgoal_tac "n = 0")
       prefer 2
      subgoal 
        apply (metis drop_Cons' drop_Nil list.discI)
        done
      apply auto
      apply hypsubst_thin
      apply (subst produce.code)
      apply (simp split: option.splits)
      apply (subst (1 2) produce_inner.simps)
      apply (auto split: prod.splits)
      using image_iff apply fastforce
      done
    done
  done

lemma produce_skip_n_productions_op_sync_op_LE_EX:
  "produce (skip_n_productions_op (sync_op buf) n) lxs = LCons (Data wm batch) lxs' \<Longrightarrow>
   t \<in> ts lxs wm \<or> t \<in> fst ` set buf \<Longrightarrow>
   t \<le> wm \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   productive lxs \<Longrightarrow>
   \<exists> n' \<le> n. \<exists>wm' batch' lxs'. produce (skip_n_productions_op (sync_op buf) n') lxs = LCons (Data wm' batch') lxs' \<and> t \<in> fst ` set batch'"
  apply (subst (asm) produce.code)
  apply (simp split: event.splits prod.splits option.splits)
  subgoal for x2 op x2a x2b xs lxs'
    apply hypsubst_thin
    apply (frule produce_inner_skip_n_productions_op_sync_op_xs)
     apply simp
    apply hypsubst_thin
    apply (frule produce_inner_skip_n_productions_op_sync_op_smaller)
         apply simp_all
    done
  done

subsection \<open>ltaken_Data Soundness\<close> 
lemma produce_skip_n_productions_op_sync_op_LE_EX_ltaken_Data:
  "\<exists> n'\<le>n . produce (skip_n_productions_op op n') lxs = LCons (Data wm batch) lxs' \<Longrightarrow>
   (wm, batch) \<in> set (ltaken_Data (Suc n) (produce op lxs))"
  apply (subst (asm) produce_skip_n_productions_op_correctness)
  apply (elim exE conjE)
  using ldropn_LCons_ltaken_Data apply fast
  done

lemma produce_skip_n_productions_op_sync_op_ltaken_Data_LE_EX:
  "(wm, batch) \<in> set (ltaken_Data (Suc n) (produce op lxs)) \<Longrightarrow>
   \<exists> n'\<le>n . \<exists> lxs' . produce (skip_n_productions_op op n') lxs = LCons (Data wm batch) lxs'"
  apply (subst produce_skip_n_productions_op_correctness)
  using in_ltaken_Data_ldropn_LCons apply fast
  done

lemma ltaken_Data_produce_sync_op_in_batch_LE:
  "monotone lxs WM \<Longrightarrow>
   productive lxs \<Longrightarrow>
   (wm, batch) \<in> set (ltaken_Data n (produce (sync_op buf) lxs)) \<Longrightarrow>
   t \<in> fst ` set batch \<Longrightarrow> t \<le> wm"
  apply (induct n arbitrary: buf lxs)
   apply auto
  subgoal premises prems for n buf lxs b
    using prems(2-) apply -
    apply (subst (asm) produce.code)
    apply (auto split: option.splits)
    apply (frule produce_inner_sync_op_specify_Some)
     apply assumption+
    apply (elim conjE exE)
    apply simp
    apply (frule produce_inner_sync_op_inversion)
    apply (elim conjE exE disjE)
     apply hypsubst_thin
     apply (meson produce_inner_sync_op_batch_le)
    apply (metis ltaken_Data_LCons_Watermark diff_le_self ldrop_enat ltaken_Data_in_Suc prems(1) productive_ldrop strict_monotone_ldrop)
    done
  done

lemma timestamp_in_taken_Data_inversion:
  "monotone lxs WM \<Longrightarrow>
   productive lxs \<Longrightarrow>
   t \<in> fst ` (\<Union>a\<in>set (ltaken_Data n (produce (sync_op buf) lxs)). set (snd a)) \<Longrightarrow>
   \<exists> wm \<ge> t . \<exists> batch . (wm, batch) \<in> set (ltaken_Data n (produce (sync_op buf) lxs)) \<and> t \<in> fst ` set batch"
  using timestamp_in_taken_Data_inversion_aux ltaken_Data_produce_sync_op_in_batch_LE
  apply fast
  done

lemma in_ltaken_Data_Watermark_in_lxs:
  "(wm, batch) \<in> set (ltaken_Data n (produce (sync_op buf) lxs)) \<Longrightarrow>
   Watermark wm \<in> lset lxs"
  apply (meson le_SucI less_or_eq_imp_le ltaken_Data_in_Suc produce_skip_n_productions_op_Some_Data_Watermark_in_LCons produce_skip_n_productions_op_sync_op_ltaken_Data_LE_EX)
  done

lemma ltaken_Data_sync_description:
  "monotone lxs WM \<Longrightarrow>
   productive lxs \<Longrightarrow>
   (wm, batch) \<in> set (ltaken_Data n (produce (sync_op buf) lxs)) \<Longrightarrow>
   fst ` set batch = sync_ts lxs wm \<union> {t \<in> fst ` set buf. t \<le> wm \<and> (\<forall>x\<in>ws lxs wm. \<not> t \<le> x)} \<and>
   (\<forall> t \<in> ts lxs wm . \<exists> wm' batch' . (wm', batch') \<in> set (ltaken_Data n (produce (sync_op buf) lxs)) \<and> t \<in> fst ` set batch') \<and> 
   (\<forall> t \<in> {t \<in> fst ` set buf . t \<le> wm} . \<exists> wm' batch' . (wm', batch') \<in> set (ltaken_Data n (produce (sync_op buf) lxs)) \<and> t \<in> fst ` set batch')"
  apply (rule conjI)
  subgoal
    apply (cases n)
     apply simp
    subgoal for n'
      apply hypsubst_thin
      apply (drule produce_skip_n_productions_op_sync_op_ltaken_Data_LE_EX)
      apply (elim exE conjE)
      subgoal for n'' lxs'
        using produce_sync_op_soundness_timestamps_aux
          [where n=n'' and buf=buf and lxs=lxs and wm=wm and batch=batch and x="Data wm batch" and WM=WM] apply simp
        done
      done
    done
  apply (rule conjI)
  subgoal
    apply (intro ballI)
    subgoal for t
      apply (cases n)
       apply simp
      subgoal for n'
        apply hypsubst_thin
        apply (frule produce_skip_n_productions_op_sync_op_ltaken_Data_LE_EX)
        apply (elim exE conjE)
        subgoal for n'' lxs'
          apply (frule produce_skip_n_productions_op_sync_op_LE_EX[where t=t])
              apply simp
             apply (meson dual_order.refl in_ltaken_Data_Watermark_in_lxs ts_le)
            apply assumption+
          apply (meson order_trans produce_skip_n_productions_op_sync_op_LE_EX_ltaken_Data)
          done
        done
      done
    done
  subgoal
    apply (intro ballI)
    subgoal for t
      apply (cases n)
       apply simp
      subgoal for n'
        apply hypsubst_thin
        apply (frule produce_skip_n_productions_op_sync_op_ltaken_Data_LE_EX)
        apply (elim exE conjE)
        subgoal for n'' lxs'
          apply (frule produce_skip_n_productions_op_sync_op_LE_EX[where t=t and WM=WM])
              apply simp
             apply fast
            apply assumption+
          apply (meson order_trans produce_skip_n_productions_op_sync_op_LE_EX_ltaken_Data)
          done
        done
      done
    done
  done                 

(* FIXME: Remove productive *)
lemma produce_sync_op_ts_le_1:
  "t \<le> wm \<Longrightarrow>
   (wm, batch) \<in> set (ltaken_Data n (produce (sync_op buf) lxs)) \<Longrightarrow>
   t \<in> fst ` set batch \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   productive lxs \<Longrightarrow>
   ts lxs t \<union> {t' \<in> fst ` set buf. t' \<le> t} \<subseteq> {t' \<in> fst ` (\<Union>a\<in>set (ltaken_Data n (produce (sync_op buf) lxs)). set (snd a)). t' \<le> t}"
  apply (frule ltaken_Data_sync_description)
    apply assumption+
  apply (elim exE conjE)
  apply auto
  subgoal for x
    apply (drule bspec[of _ _ x])
     apply (rule in_ts_transitive)
      apply assumption
     apply (meson subsetD sync_ts_subset_ts)
    apply (metis (no_types, lifting) UN_iff image_UN snd_conv)
    done
  subgoal for x
    apply (rule ts_le)
    apply assumption+
    done
  subgoal for t' d
    apply (smt (verit) UN_iff fst_conv image_UN image_eqI order_trans snd_conv)
    done
    apply (metis (no_types, lifting) UN_iff image_UN snd_conv ts_le_2)
  subgoal for t' d
    apply (rule ts_le)
    apply assumption+
    done
  subgoal for t' d
    apply (smt (verit) UN_iff fst_conv image_UN image_eqI order_trans snd_conv)
    done
  done

(* FIXME: Remove productive *)
lemma produce_sync_op_ts_le_2:
  "t \<le> wm \<Longrightarrow>
   (wm, batch) \<in> set (ltaken_Data n (produce (sync_op buf) lxs)) \<Longrightarrow>
   t \<in> fst ` set batch \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   productive lxs \<Longrightarrow>
   {t' \<in> fst ` (\<Union>a\<in>set (ltaken_Data n (produce (sync_op buf) lxs)). set (snd a)). t' \<le> t} \<subseteq> ts lxs t \<union> {t' \<in> fst ` set buf. t' \<le> t}"
  apply (frule ltaken_Data_sync_description)
    apply assumption+
  apply (elim exE conjE)
  apply (intro subsetI)
  apply simp
  subgoal for t'
    apply (cases n)
     apply simp
    subgoal for n'
      apply hypsubst_thin
      apply (frule timestamp_in_taken_Data_inversion[where t=t' and n="Suc n'"])
        apply assumption+
       apply auto[1]
      apply (elim exE conjE)
      subgoal for wm' batch'
        apply (drule produce_skip_n_productions_op_sync_op_ltaken_Data_LE_EX[where batch=batch'])
        apply (elim conjE exE)
        subgoal for n'' lxs'
          apply (frule produce_skip_n_productions_op_sync_op_in_ts_or_buf)
              apply (meson dual_order.refl produce_skip_n_productions_op_Some_Data_Watermark_in_LCons)
             apply assumption+
          subgoal premises prems
            using prems(1,2,4-) apply -
            apply (elim disjE)
            subgoal
              apply (rule disjI1)
              apply (rule ts_change_t[of _ wm'])
                apply assumption+
              done
            apply simp
            done
          done
        done
      done
    done
  done

(* FIXME: Remove productive *)
lemma produce_sync_op_ts_le:
  "t \<le> wm \<Longrightarrow>
   (wm, batch) \<in> set (ltaken_Data n (produce (sync_op buf) lxs)) \<Longrightarrow>
   t \<in> fst ` set batch \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   productive lxs \<Longrightarrow>
   ts lxs t \<union> {t' \<in> fst ` set buf. t' \<le> t} = {t' \<in> fst ` (\<Union>a\<in>set (ltaken_Data n (produce (sync_op buf) lxs)). set (snd a)). t' \<le> t}"
  apply (smt (verit, ccfv_SIG) Collect_cong le_iff_sup produce_sync_op_ts_le_1 produce_sync_op_ts_le_2 sup.order_iff)
  done

lemma produce_inner_skip_n_productions_op_sync_op_coll_list_batch:
  "produce_inner (skip_n_productions_op (sync_op buf) n', lxs) = Some (op, x, xs, lxs') \<Longrightarrow>
   x = Data wm batch \<Longrightarrow>
   xs = [Watermark wm] \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   n' \<le> n \<Longrightarrow>
   t \<in> fst ` set batch \<Longrightarrow>
   coll_list (concat (map snd (ltaken_Data (Suc n) (produce (sync_op buf) lxs)))) t = coll_list batch t"
  subgoal premises prems
    using prems apply -
    apply (induct "(skip_n_productions_op (sync_op buf) n', lxs)" "(op, x, xs, lxs')" arbitrary: lxs lxs' op buf x xs n n' rule: produce_inner_alt)
    using prems apply simp
    subgoal for h lxs' lgc' lxs'a op buf x xs n' n
      apply (simp split: event.splits if_splits option.splits)
      subgoal for t' d
        apply hypsubst_thin
        apply (drule meta_spec)
        apply (drule meta_spec)
        apply (drule meta_spec[of _ "n"])
        apply (drule meta_mp)
         apply (rule refl)
        apply (drule meta_mp)
        subgoal
          apply (subst (asm) produce_inner.simps)
          apply auto
          done
        apply (drule meta_mp)
        using strict_monotone_drop_head apply blast
        apply (drule meta_mp)
         apply simp
        apply (simp add: produce_Data)
        done
      subgoal for t' d
        apply hypsubst_thin
        apply (cases n)
         apply simp
        subgoal for n'
          apply hypsubst_thin
          apply simp
          apply (drule meta_spec)
          apply (drule meta_spec[of _ "0"])
          apply (drule meta_spec[of _ "Suc n'"])
          apply (drule meta_mp)
           apply simp
          apply (drule meta_mp)
          subgoal
            apply (subst (asm) produce_inner.simps)
            apply auto
            done
          apply (drule meta_mp)
          using strict_monotone_drop_head apply blast
          apply (drule meta_mp)
          subgoal
            apply (subst (asm) produce_inner.simps)
            apply auto
            done
          apply (subst (asm) produce_inner.simps)
          apply auto
          done
        done
      subgoal for wm'
        apply hypsubst_thin
        apply (drule meta_spec)
        apply (drule meta_spec)
        apply (drule meta_spec[of _ "n - Suc (Suc 0)"])
        apply (drule meta_mp)
         apply (rule refl)
        apply (drule meta_mp)
        subgoal
          apply (subst (asm) produce_inner.simps)
          apply auto
          done
        apply (drule meta_mp)
        using strict_monotone_drop_head apply blast
        apply (drule meta_mp)
         apply simp
        apply (simp add: in_buf_produce_Watermark)
        apply (subst produce_inner_skip_n_productions_op_sync_op_coll_list_filter_Nil)
               apply assumption
              apply (rule refl)
             apply (rule refl)
            apply assumption+
         apply simp
        apply (simp add: in_buf_produce_Watermark Suc_diff_Suc ltaken_Data_LCons_Watermark numeral_2_eq_2)
        done
      subgoal for wm'
        apply hypsubst_thin
        apply (drule meta_spec)
        apply (drule meta_spec)
        apply (drule meta_spec[of _ "n"])
        apply (drule meta_mp)
         apply (rule refl)
        apply (drule meta_mp)
        subgoal
          apply (subst (asm) produce_inner.simps)
          apply auto
          done
        apply (drule meta_mp)
        using strict_monotone_drop_head apply blast
        apply (drule meta_mp)
         apply simp
        apply (simp add: not_in_buf_produce_Watermark)
        done
      subgoal for wm'
        apply hypsubst_thin
        apply (drule meta_spec)
        apply (drule meta_spec[of _ 0])
        apply (drule meta_spec[of _ "n - Suc (Suc 0)"])
        apply (drule meta_mp)
         apply simp
        apply (drule meta_mp)
        subgoal
          apply (subst (asm) produce_inner.simps)
          apply auto
          done
        apply (drule meta_mp)
        using strict_monotone_drop_head apply blast
        apply (drule meta_mp)
         apply simp
        apply (simp add: in_buf_produce_Watermark ltaken_Data_LCons_Watermark)
        apply (subst produce_inner_skip_n_productions_op_sync_op_coll_list_filter_Nil)
               apply assumption
              apply (rule refl)
             apply (rule refl)
            apply assumption+
         apply simp
        apply (simp add: Suc_diff_Suc)
        done
      subgoal for wm'
        apply hypsubst_thin
        apply (drule meta_spec)
        apply (drule meta_spec[of _ 0])
        apply (drule meta_spec[of _ "n"])
        apply (drule meta_mp)
         apply simp
        apply (drule meta_mp)
        subgoal
          apply (subst (asm) produce_inner.simps)
          apply auto
          done
        apply (drule meta_mp)
        using strict_monotone_drop_head apply blast
        apply (drule meta_mp)
         apply simp
        apply (simp add: in_buf_produce_Watermark ltaken_Data_LCons_Watermark)
        apply (subst (asm) produce_inner.simps)
        apply auto
        apply (simp add: ltaken_Data_LCons_Watermark)
        done
      done
    subgoal premises prems for h x xs lxs' lgc' buf n' n
      using prems apply -
      apply (subst produce.code)
      apply (auto split: prod.splits event.splits if_splits option.splits)
      subgoal
        apply (subst (asm) produce_inner.simps)
        apply (auto split: event.splits if_splits option.splits)
        apply (metis prems(2) produce_inner_skip_n_productions_op_Some_produce_inner_None)
        done
      subgoal for x2 a b aa ab ac lxs'
        apply (subgoal_tac "n' = 0")
         defer
         apply (metis drop0 drop_Suc_Cons less_2_cases list.discI not_less_iff_gr_or_eq numeral_2_eq_2)
        apply (subst (asm) (1 2) produce_inner.simps)
        apply (auto split: event.splits if_splits option.splits)
        apply hypsubst_thin
        apply (rule coll_list_concat_ltaken_Data_Nil)
        apply auto
        subgoal for aa ba wm' batch' baa
          using produce_no_timestamps_out_of_the_blue[where n=0 and buf="filter (\<lambda>(t, _). \<not> t \<le> wm) buf" and t=t and wm=wm' and batch=batch'] apply simp
          apply (smt (verit, ccfv_SIG) Data_tail_ahead_of_t case_prod_unfold fst_conv image_iff mem_Collect_eq)
          done
        done
      done
    done
  done

lemma produce_skip_n_productions_op_sync_op_coll_list_batch:
  "produce (skip_n_productions_op (sync_op buf) n') lxs = LCons (Data wm batch) lxs' \<Longrightarrow>
   t \<in> fst ` set batch \<Longrightarrow>
   t \<in> ts lxs wm \<or> t \<in> fst ` set buf \<Longrightarrow>
   n' \<le> n \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   coll_list (concat (map snd (ltaken_Data (Suc n) (produce (sync_op buf) lxs)))) t = coll_list batch t"
  apply (subst (asm) produce.code)
  apply (simp split: prod.splits option.splits)
  subgoal for op xs lxs'' d
    apply hypsubst_thin
    apply (rule produce_inner_skip_n_productions_op_sync_op_coll_list_batch[where t=t])
         apply assumption
        apply (rule refl)
    using produce_inner_skip_n_productions_op_sync_op_xs apply blast
      apply assumption+
    done
  done

lemma not_timestmap_out_of_the_blue_ltaken_Data:
  "t' \<notin> ts lxs wm \<Longrightarrow> t' \<notin> fst ` set buf \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   t \<le> wm \<Longrightarrow>
   (wm, batch) \<in> set (ltaken_Data (Suc n) (produce (sync_op buf) lxs)) \<Longrightarrow>
   t' \<le> t \<Longrightarrow>
   set (coll_list (concat (map snd (ltaken_Data (Suc n) (produce (sync_op buf) lxs)))) t') = {}"
  unfolding coll_list_def
  apply auto
  apply (drule produce_skip_n_productions_op_sync_op_ltaken_Data_LE_EX)
  apply (elim conjE exE)
  subgoal for b wm' batch n' lxs'
    apply (frule produce_skip_n_productions_op_does_not_produce_out_of_the_blue[where t=t'])
      apply auto
    apply (smt (verit, ccfv_SIG) dual_order.refl fst_conv imageI order_trans produce_skip_n_productions_op_Some_Data_Watermark_in_LCons produce_skip_n_productions_op_does_not_produce_out_of_the_blue produce_skip_n_productions_op_sync_op_ltaken_Data_LE_EX ts_change_t ts_le)
    done
  done

(* FIXME: Remove productive *)
lemma ltaken_Data_produce_soundness:
  "monotone lxs WM \<Longrightarrow>
   productive lxs \<Longrightarrow>
   t \<le> wm \<Longrightarrow>
   (wm, batch) \<in> set (ltaken_Data (Suc n) (produce (sync_op buf) lxs)) \<Longrightarrow>
   t \<in> fst ` set batch \<Longrightarrow>
   t' \<le> t \<Longrightarrow> 
   coll lxs t' + mset (coll_list buf t') = mset (coll_list (concat (map snd (ltaken_Data (Suc n) (produce (sync_op buf) lxs)))) t')"
  apply (frule produce_skip_n_productions_op_sync_op_ltaken_Data_LE_EX)
  apply (cases "t' \<in> ts lxs wm \<or> t' \<in> fst ` set buf")
  subgoal
    apply (elim exE conjE)
    subgoal for n' lxs'
      apply (drule produce_skip_n_productions_op_sync_op_LE_EX[where t=t'])
          apply assumption+
         apply simp
        apply assumption+
      apply (elim exE conjE)
      subgoal for n'' wm' batch' lxs'
        apply (frule produce_skip_n_productions_op_sync_op_sync_op_soundness_LCons)
           apply assumption+
         apply (rule refl)
        apply (elim conjE)
        apply (subst produce_skip_n_productions_op_sync_op_coll_list_batch)
             apply assumption+
           apply (meson dual_order.eq_iff dual_order.trans in_ltaken_Data_Watermark_in_lxs ts_change_t)
          apply simp
         apply assumption+ 
        apply (rule produce_skip_n_productions_op_sync_op_coll_soundness)
          apply assumption+
        done
      done
    done
  apply (elim exE conjE)
  subgoal for n' lxs'
    apply (subgoal_tac "coll lxs t'= {#}")
     defer
     apply (meson dual_order.refl finite_ts in_ltaken_Data_Watermark_in_lxs not_in_ts_coll_empty order_trans)
    apply (subgoal_tac "coll_list buf t' = []")
     defer
    subgoal
      unfolding coll_list_def
      apply (simp add: image_iff)
      done
    apply simp
    apply auto
    using not_timestmap_out_of_the_blue_ltaken_Data apply blast
    done
  done

lemma produce_inner_skip_n_productions_op_Some_Data_in:
  "produce_inner (skip_n_productions_op (sync_op buf) n, lxs) = Some (lgc', x, xs, lxs') \<Longrightarrow>
   x = Data wm batch \<Longrightarrow>
   (t, d) \<in> set batch \<Longrightarrow>
   Data t d \<in> lset lxs \<or> (t, d) \<in> set buf"
 apply (induct "(skip_n_productions_op (sync_op buf) n, lxs)" "(lgc', x, xs, lxs')" arbitrary: n buf lxs lxs' xs batch wm lgc' rule: produce_inner_alt[consumes 1])
  subgoal for h lxs' lgc' n buf lxs'a xs lgc'a batch wm
    apply (auto split: if_splits event.splits)
          apply fastforce+
       apply (metis fst_conv rotate1.simps(2) set_ConsD set_rotate1 skip_n_productions_op_0)
    apply (metis rotate1.simps(2) set_ConsD set_rotate1 skip_n_productions_op_0 snd_conv)
    apply (metis filter_is_subset skip_n_productions_op_0 subset_code(1))
    apply (metis skip_n_productions_op_0)
    done
  subgoal for h xs lxs' lgc' n buf batch wm
    apply hypsubst_thin
    apply (auto split: if_splits event.splits)
    apply (subgoal_tac "n = 1 \<or> n = 0")
     defer
     apply (metis (mono_tags, lifting) One_nat_def Suc_lessI add.commute bot_nat_0.not_eq_extremum drop_eq_Nil2 leI list.discI list.size(3) list.size(4) plus_1_eq_Suc)
    apply (elim disjE)
     apply (auto split: if_splits event.splits)
    done
  done

lemma produce_skip_n_productions_op_Some_Data_in_LCons:
  "produce (skip_n_productions_op (sync_op buf) n) lxs = LCons x xs \<Longrightarrow>
   x = Data wm batch \<Longrightarrow>
   (t, d) \<in> set batch \<Longrightarrow>
   Data t d \<in> lset lxs \<or> (t, d) \<in> set buf"
  apply (subst (asm) produce.code)
  apply (auto split: option.splits)
  using produce_inner_skip_n_productions_op_Some_Data_in apply fast
  done

lemma in_ltaken_Data_in_lxs:
  "(wm, batch) \<in> set (ltaken_Data n (produce (sync_op buf) lxs)) \<Longrightarrow>
   (t, d) \<in> set batch \<Longrightarrow>
   Data t d \<in> lset lxs \<or> (t, d) \<in> set buf"
  by (meson Suc_le_mono le_Suc_eq ltaken_Data_in_Suc produce_skip_n_productions_op_Some_Data_in_LCons produce_skip_n_productions_op_sync_op_ltaken_Data_LE_EX)

subsection \<open>Strict monotone proofs\<close>
lemma produce_sync_op_strict_monotone:
  "monotone stream_in WM \<Longrightarrow>
   produce (sync_op buf) stream_in = stream_out \<Longrightarrow> 
   monotone stream_out WM"
  apply (coinduction arbitrary: stream_in WM stream_out buf rule: strict_monotone_coinduct_shift_strict_monotone_prepend_cong1)
  subgoal for stream_in WM stream_out buf
    apply (subst (asm) produce.corec.code)
    apply (subst produce.corec.code)
    apply (simp split: option.splits prod.splits)
    apply hypsubst_thin
    apply (frule produce_inner_sync_op_inversion_2)
    apply (elim exE conjE)
    apply hypsubst_thin
    subgoal premises prems for x2 lgc' x2a x xs' xs lxs buf'
      using prems(2,1) apply -
      apply (induct "(sync_op buf, stream_in)" "(sync_op buf', x, xs, lxs)" arbitrary: buf stream_in lxs buf' rule: produce_inner_alt)
      subgoal using prems by simp
      subgoal premises temp for h lxs' lgc' buf lxs buf'
        using temp(1,3,4) apply -
        apply (subst (asm) produce_inner.simps)
        apply (simp split: llist.splits event.splits if_splits)
        subgoal for t d
          using temp(2) apply hypsubst_thin
          apply (drule meta_spec[of _ "buf @ [(t, d)]"])
          apply (drule meta_spec[of _ "buf'"])
          apply (drule meta_mp)
           apply (rule refl)
          apply (drule meta_mp)
           apply (rule refl)
          apply (drule meta_mp)
           apply assumption
          apply (drule meta_mp)
          using strict_monotone_drop_head apply blast
          apply force
          done
        subgoal for wm
          using temp(2) apply hypsubst_thin
          apply (drule meta_spec[of _ "buf"])
          apply (drule meta_spec[of _ "buf'"])
          apply (drule meta_mp)
           apply (rule refl)
          apply (drule meta_mp)
           apply (rule refl)
          apply (drule meta_mp)
           apply assumption
          apply (drule meta_mp)
          using strict_monotone_drop_head apply blast
          apply force
          done
        done
      subgoal for h lxs' buf buf'
        apply (subst (asm) produce_inner.simps)
        apply (simp split: llist.splits event.splits if_splits)
        subgoal for wm
          apply (elim conjE)
          apply hypsubst_thin
          apply simp
          apply (rule exI[of _ "produce (sync_op buf') lxs'"])
          apply (rule exI[of _ "[Data wm (filter (\<lambda>(t, _). t \<le> wm) buf), Watermark wm]"])
          apply simp
          apply safe
            apply (metis LConsWatermark monotone.simps)
          using LConsWatermark apply blast
          apply (rule monotone_prepend_cong_base)
          apply (rule exI[of _ lxs'])
          apply safe
          using LConsWatermark apply blast
          apply (rule exI[of _ buf'])
          apply safe
           apply (subst produce.corec.code)
           apply simp
          apply (subst (2) produce.corec.code)
          apply simp
          done
        done
      done
    done
  done

subsection \<open>Productive proofs\<close> 
lemma produce_sync_op_productive:
  "productive stream_in \<Longrightarrow>
   produce (sync_op buf) stream_in = stream_out \<Longrightarrow> 
   productive stream_out"
  apply (coinduction arbitrary: stream_in stream_out buf rule: productive_coinduct_prepend_cong1_shift)
  subgoal for stream_in stream_out buf
    apply hypsubst_thin
    apply (subst (1 2) produce.corec.code)
    apply (simp split: option.splits prod.splits)
    apply (rule allI impI)+
    apply (frule produce_inner_sync_op_inversion_2)
    apply (elim exE conjE)
    apply simp
    apply hypsubst_thin
    subgoal premises prems for a x xs lxs buf'
      using prems(2,1) apply -
      apply (induct "(sync_op buf, stream_in)" arbitrary: buf stream_in lxs rule: produce_inner_alt[where y="(sync_op buf', x, xs, lxs)"])
      using prems apply simp
      subgoal premises temp for h lxs' lgc' buf'' lxs''
        using temp(1,3-) apply -
        apply (subst (asm) produce_inner.simps)
        apply (simp split: llist.splits event.splits if_splits)
        subgoal for t d
          using temp(2) apply hypsubst_thin
          apply (drule meta_spec)+
          apply (drule meta_mp)
           apply (rule refl)
          apply (drule meta_mp)
           apply assumption
          apply (drule meta_mp)
          using productive_drop_head apply blast
          apply (simp add: produce_Data)
          done
        subgoal for wm
          using temp(2) apply hypsubst_thin
          apply (drule meta_spec)+
          apply (drule meta_mp)
           apply (rule refl)
          apply (drule meta_mp)
           apply assumption
          apply (drule meta_mp)
          using productive_drop_head apply blast
          apply (simp add: not_in_buf_produce_Watermark)
          done
        done
      subgoal for h x xs lxs' lgc' buf lxs
        apply (drule sync_op_buf_some_out_lgc_preserves)
        apply (elim conjE exE)
        apply hypsubst_thin
        apply (subst (asm) produce_inner.simps)
        apply (simp split: llist.splits event.splits if_splits)
        apply (elim exE disjE conjE)
        apply hypsubst_thin
        apply (rule verit_forall_inst(6))
        apply (rule impI)
        apply simp
        apply (metis (mono_tags, lifting) productive_drop_head productive_prepend_cong1_base)
        done
      done
    done
  done


subsection \<open>Completeness proofs\<close> 
lemma produce_sync_op_from_buf:
  "x \<in> lset lxs \<Longrightarrow>
   x = Watermark wm \<Longrightarrow>
   (t, d) \<in> set buf \<Longrightarrow>
   t \<le> wm \<Longrightarrow>
   \<exists> wm' d. Data wm' d \<in> lset (produce (sync_op buf) lxs) \<and> t \<in> fst ` set d"
  apply (induct lxs arbitrary: buf rule: lset_induct)
  subgoal for xs buf
    apply (subst produce.code)
    apply (subst produce_inner.simps)
    apply (auto split: llist.splits event.splits option.splits)
     apply (metis (no_types, lifting) case_prodI2 fst_conv image_iff mem_Collect_eq set_filter)
    apply (metis (no_types, lifting) case_prodI fst_conv image_eqI mem_Collect_eq set_filter)
    done
  subgoal for x' xs buf
    apply (cases x')
     defer
    subgoal for wm'
      apply hypsubst_thin
      apply (cases " \<exists>(t, d)\<in>set buf. t \<le> wm'")
      subgoal
        apply (cases "t \<le> wm'")
         defer
        subgoal premises p2
          using p2(1,2,4-) apply -
          apply (subst in_buf_produce_Watermark)
           apply simp
          using p2(3)[where buf="filter (\<lambda>(t, _). \<not> t \<le> wm') buf"] apply -
          apply (drule meta_mp)
           apply simp
          apply (drule meta_mp)
           apply simp
          apply (meson llist.set_intros(2) strict_monotone_drop_head)
          done
        subgoal premises p2
          using p2(1,2,4-) apply -
          apply (subst in_buf_produce_Watermark)
           apply assumption
          using image_iff apply fastforce
          done
        done
      subgoal
        apply (drule meta_spec)+
        apply (drule meta_mp)
         apply simp
        apply (drule meta_mp)
         apply assumption
        apply (drule meta_mp)
         apply assumption
        apply (subst not_in_buf_produce_Watermark)
         apply simp
        apply assumption
        done
      done
    subgoal for t d
      apply (drule meta_spec[of _ "buf @ [(t, d)]"])
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
       apply simp
      apply (drule meta_mp)
       apply assumption
      apply (simp add: produce_Data)
      done
    done
  done

lemma produce_inner_None_finite_aux:
  "produce_inner (sync_op buf, lxs) = None \<Longrightarrow>
   productive lxs \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   \<not> lfinite lxs \<Longrightarrow>
   False"
  apply (subgoal_tac "lfinite lxs \<or> (\<exists> n t d . lnth lxs n = Data t d)")
   defer
  subgoal 
    unfolding productive_def
    apply (metis alwll.cases evll_wholdsll_finds_n_alt is_Data_def lfinite_LNil)
    done
  apply simp
  apply safe
  subgoal for n t d
    apply (frule productive_finds_data)
      apply assumption+
    apply safe
    subgoal for m wm
      apply (frule produce_inner_conditions_to_produce[where m=n and n=m and d=d and buf=buf])
          apply assumption+
         apply (simp add: not_lfinite_llength)
        apply assumption
       apply (rule disjI2)
       apply fast
      apply simp
      done
    done
  done

lemma produce_inner_None_finite:
  "produce_inner (sync_op buf, lxs) = None \<Longrightarrow>
   productive lxs \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   lfinite lxs"
  using produce_inner_None_finite_aux by blast

find_theorems the_enat 

(* FIXME: monotone could be removed *)
lemma sync_completeness_gen_aux:
  "(\<exists> i d. enat i < llength lxs \<and> lnth lxs i = Data t d \<and> j = Suc i) \<or> j = 0 \<and> (\<exists> d. (t, d) \<in> set buf) \<Longrightarrow>
  \<forall> (t', d) \<in> set buf . lfinite lxs \<or> (\<exists> wm \<ge> t' . Watermark wm \<in> lset lxs) \<Longrightarrow>
  monotone lxs WM \<Longrightarrow>
  productive lxs \<Longrightarrow>
  \<exists> wm out. Data wm out \<in> lset (produce (sync_op buf) lxs) \<and> t \<in> fst ` set out \<or>
  lfinite lxs \<and> (\<forall> k  \<in> {j ..< the_enat (llength lxs)} . \<not> (\<exists> t' \<ge> t . lnth lxs k = Watermark t'))"  
  apply (induct j arbitrary: lxs buf)
  subgoal for lxs buf
    apply simp
    apply (cases "\<exists> wm \<ge> t . Watermark wm \<in> lset lxs")
     apply (elim exE)
    subgoal for d wm
      apply (rule disjI1)
      using produce_sync_op_from_buf[of "Watermark wm" lxs wm t d buf] apply (auto)
      done
    subgoal
      apply (rule disjI2)
      apply (rule conjI)
       apply safe
       apply blast
      apply (metis (no_types, opaque_lifting) atLeastLessThan_iff order.strict_iff_not enat_ile enat_ord_simps(2) in_lset_conv_lnth linorder_linear the_enat.simps)
      done
    done
  subgoal for j' lxs buf
    apply simp
    apply (subgoal_tac "\<not> lnull lxs")
     prefer 2
    subgoal
      by (cases lxs; auto)
    apply (cases j')
     apply simp
     apply (elim exE conjE)
    subgoal premises prems for d
      using prems(1)[where lxs="ltl lxs" and buf="buf @ [(t, d)]"]
      apply -
      apply (drule meta_mp)
       apply auto[1]
      apply (drule meta_mp)
       apply auto[1]
      subgoal
        using prems(2-) apply -
        by (metis (no_types, lifting) enat_ord_code(4) event.distinct(1) in_lset_conv_lnth insert_iff lfinite.simps llist.exhaust_sel llist.simps(19) lnth_0 not_lfinite_llength productive_finds_data)
      subgoal
        using prems(2-) apply -
        by (smt (verit) case_prod_conv event.distinct(1) insert_iff lfinite.simps llist.exhaust_sel llist.simps(19) lnth_0)
      apply (drule meta_mp)
      using prems(2-) strict_monotone_ltl apply blast
      apply (drule meta_mp)
      using prems(2-) apply (metis lhd_LCons_ltl productive_drop_head)
      apply (erule disjE)
       apply (rule disjI1)
      using produce_lhd_data
       apply (metis lhd'_simps(2) lhd_LCons_ltl lnth_0 prems(5) prems(8))
      apply (rule disjI2)
      using prems(2-) apply (auto simp add: lnth_0_conv_lhd Suc_le_eq Suc_less_eq2 gr0_conv_Suc lnth_ltl llength_ltl)
      apply (metis atLeastLessThan_iff bot_nat_0.extremum co.enat.sel(2) eSuc_enat lfinite_conv_llength_enat the_enat.simps)
      done
    subgoal for n'
      apply simp
      apply (cases "lhd' lxs")
       apply (metis lhd'_def option.distinct(1))
      subgoal for h
        apply (cases h)
        subgoal for t' d
          subgoal premises prems
            using prems(1)[where lxs="ltl lxs" and buf="buf @ [(t', d)]"]
            apply -
            apply (drule meta_mp)
            subgoal using prems(2-) 
              by (simp add: Suc_ile_eq Utils.llength_eSuc_ltl lnth_ltl)
            apply (drule meta_mp)
            subgoal
              apply auto[1]
              subgoal using prems(2-) apply -
                apply (drule productive_ldrop[where n=j'])
                apply (metis (no_types, opaque_lifting) enat_ord_code(4) event.distinct(1) in_lset_conv_lnth insert_iff lfinite.simps lhd'_simps(2) llist.exhaust_sel llist.simps(19) not_lfinite_llength option.inject prems(5) productive_finds_data)
                done
              subgoal 
                using prems(2-) apply -
                apply (drule productive_ldrop[where n=j'])
                by (smt (verit, del_insts) case_prodD event.distinct(1) lhd'_simps(2) lset_cases ltl_simps(2) option.inject)
              done
            apply (drule meta_mp)
            using prems(2-) using strict_monotone_ltl apply blast
            apply (drule meta_mp)
            using prems(2-) apply (metis lhd_LCons_ltl productive_drop_head)
            apply (erule disjE)
             apply (rule disjI1)
            subgoal
              using prems(2-)
              apply (simp add: produce_lhd_data)
              done
            subgoal
              apply (rule disjI2)
              apply simp
              using prems(2-) apply (auto simp add: lnth_0_conv_lhd Suc_le_eq Suc_less_eq2 gr0_conv_Suc lnth_ltl llength_ltl)
              apply (metis Suc_le_eq atLeastLessThan_iff co.enat.sel(2) eSuc_enat lfinite_llength_enat the_enat.simps)
              done
            done
          done
        subgoal for wm'
          apply hypsubst_thin
          subgoal premises prems
            apply (subst produce.code)
            using prems(7) apply (simp only: Let_def split: option.splits event.splits prod.splits list.splits)
            apply (rule conjI)
             apply (rule impI)
             apply (rule disjI2)
             apply (rule conjI)
            using produce_inner_None_finite prems(4) prems(5) apply blast
             apply auto[1]
            using prems(2) apply -
             apply (elim conjE exE)
            using prems(3-) apply -
            subgoal for k t d'
              apply (drule produce_inner_conditions_to_produce[where n=k and m="Suc n'" and d=d' and buf=buf])
                  apply assumption
                 apply (metis (no_types, lifting) enat_ord_simps(2) lfinite_llength_enat prems(4) produce_inner_None_finite the_enat.simps)
                apply simp
               apply simp
              apply simp
              done
            apply ((rule allI)+; (rule impI)+)
            apply hypsubst_thin
            subgoal for x2 x1 x2a x1a x2b x1b x2c
              apply (subst (asm) produce_inner.simps)
              apply (simp del: sync_op.simps split: llist.splits prod.splits list.splits option.splits)
              subgoal for x21 d lxs' x1c x2
                apply hypsubst_thin
                apply (frule sync_op_buf_order_empty_lgc_preserves)
                apply (elim exE conjE disjE)
                 apply simp_all
                apply hypsubst_thin
                subgoal for wm2
                  using prems(1)[where buf=buf and lxs=lxs'] apply -
                  apply (drule meta_mp)
                   apply (simp add: Suc_ile_eq)
                  apply (drule meta_mp)
                   apply fast
                  apply (drule meta_mp)
                   apply (meson strict_monotone_drop_head)
                  apply (drule meta_mp)
                   apply (meson productive_drop_head)
                  apply (elim exE disjE conjE)
                   apply (subst (asm) produce.code)
                   apply simp
                   apply blast
                  using Suc_le_D llength_eq_infty_conv_lfinite the_enat_eSuc apply fastforce
                  done
                done
              subgoal for x21 d x22 x2
                apply hypsubst_thin
                apply (frule sync_op_buf_some_out_lgc_preserves)
                apply (elim exE conjE disjE)
                apply hypsubst_thin
                subgoal for t' d
                  using prems(1)[where lxs=x2c and buf="filter (\<lambda>(t, _). \<not> t \<le> t') buf"] apply -
                  apply (drule meta_mp)
                  using Suc_ile_eq apply blast
                  apply (drule meta_mp)
                   apply force
                  apply (drule meta_mp)
                  using strict_monotone_drop_head apply blast
                  apply (drule meta_mp)
                  using productive_drop_head apply blast
                  apply (elim exE conjE disjE)
                  subgoal for wmm out
                    apply (subst (asm) produce.code)
                    apply (simp split: option.splits)
                    apply (subst produce.code)
                    apply (simp del: sync_op.simps split: prod.splits option.splits)
                    apply hypsubst_thin
                    apply blast
                    done
                  subgoal
                    apply (simp split: option.splits)
                    apply hypsubst_thin
                    apply (metis (no_types, opaque_lifting) image_Suc_atLeastLessThan image_iff llength_eq_infty_conv_lfinite lnth_Suc_LCons the_enat_eSuc)
                    done
                  done
                done
              done
            done
          done
        done
      done
    done
  done

lemma sync_op_completeness_aux: 
  "enat i < llength lxs \<Longrightarrow>
   lnth lxs i = Data t d\<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   productive lxs \<Longrightarrow>
   \<exists> wm out. Data wm out \<in> lset (produce (sync_op []) lxs) \<and> t \<in> fst ` set out \<or>
   lfinite lxs \<and> (\<forall> k  \<in> {Suc i ..< the_enat (llength lxs)} . \<not> (\<exists> t' \<ge> t . lnth lxs k = Watermark t'))"
  using sync_completeness_gen_aux[where buf="[]" and lxs=lxs and j="Suc i" and WM=WM] by auto

lemma sync_op_completeness: 
  "enat i < llength lxs \<Longrightarrow>
   lnth lxs i = Data t d \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   productive lxs \<Longrightarrow>
   \<exists> wm out. Data wm out \<in> lset (produce (sync_op []) lxs) \<and> mset (map snd (filter (\<lambda> (t', d) . t' = t) out)) = coll lxs t \<or>
   lfinite lxs \<and> (\<forall> k  \<in> {Suc i ..< the_enat (llength lxs)} . \<not> (\<exists> t' \<ge> t . lnth lxs k = Watermark t'))"
  apply (subgoal_tac "Data t d \<in> lset lxs")
   defer
  using in_lset_conv_lnth apply fastforce
  apply (frule sync_op_completeness_aux[where lxs=lxs and WM=WM])
     apply assumption+
  apply (elim disjE exE conjE)
  subgoal for wm out
    apply (rule exI[of _ wm])
    apply (rule exI[of _ out])
    apply (rule disjI1)
    apply simp
    apply (frule produce_sync_op_soundness)
      apply assumption+
    apply (frule produce_sync_op_soundness_timestamps)
      apply assumption+
    apply (elim conjE)
    apply fastforce
    done
  apply blast
  done

section \<open>incr_op\<close> 
primcorec incr_op where
  "incr_op buf = Logic (\<lambda> ev.
     case ev of
       Data wm batch \<Rightarrow> let ts = rev (remdups (map fst (rev batch))) ;
                        out = map (\<lambda> t . Data t (buf@ batch)) ts in
                        (incr_op (buf @ batch), out)
     | Watermark wm \<Rightarrow>  (incr_op buf, [Watermark wm])
   )"

subsection \<open>Auxialiry\<close> 
lemma produce_inner_incr_op_inversion:
  "produce_inner (incr_op buf, lxs) = Some (lgc', x, xs', lxs') \<Longrightarrow>
   \<exists> buf' n . lgc' = incr_op buf' \<and> lxs' = ldropn n lxs \<and> n > 0"
  apply (induct "(incr_op buf, lxs)" "(lgc', x, xs', lxs')" arbitrary: buf lxs rule: produce_inner_alt[consumes 1])
  subgoal for h lxs'a lgc'a buf 
    apply (auto split: event.splits)
    apply (metis ldropn_Suc_LCons zero_less_Suc)
    done
  subgoal for h buf
    apply (auto split: event.splits)
     apply force+
    done
  done

lemma produce_inner_incr_op_inversion_2:
  "produce_inner (incr_op buf, lxs) = Some (lgc', x, xs', lxs') \<Longrightarrow> \<exists> buf' . lgc' = incr_op buf'"
  using produce_inner_incr_op_inversion by blast

lemma apply_incr_op_inversion:
  "apply (incr_op buf) h = (incr_op buf', x # xs) \<Longrightarrow>
  (\<exists> wm batch . h = Data wm batch \<and> (tmp ` set (x#xs) = fst ` set batch)) \<or> ( \<exists> wm . h = Watermark wm)"
  apply (simp split: event.splits)
  apply (elim conjE)
  subgoal premises p for t d
    using p(3,2,1) apply -
    apply (drule arg_cong[where f="\<lambda> x. tmp ` set x"])
    apply simp
    apply (subst (asm) img_tmp_Lambda_Data)
     apply blast
    apply simp
    done
  apply fast
  done

lemma apply_incr_op_out_preserves:
  "apply (incr_op buf) h = (op, x#xs) \<Longrightarrow>
   \<exists> wm batch. (h = Data wm batch \<and> op = (incr_op (buf @ batch)) \<and> (\<forall> e \<in> set (x#xs) . (\<exists> t d . e = Data t d \<and> t \<in> fst ` set batch))) \<or> h = Watermark wm"
  apply (auto split: event.splits prod.splits list.splits if_splits)
   apply (metis list.set_intros(1) list.set_map rev.simps(2) set_remdups set_rev)
  apply (metis (no_types, lifting) UnI1 image_set set_append set_remdups set_rev)
  done

subsection \<open>Soundness\<close> 

lemma produce_inner_skip_n_productions_op_incr_op:
  "produce_inner (skip_n_productions_op (incr_op buf) m, lxs) = Some (lgc', x, xs, lxs') \<Longrightarrow>
   x = Data t data_coll \<Longrightarrow>
   prefix_production_LE (incr_op buf) lxs (Suc m) n \<Longrightarrow>
   data_coll = buf @ concat (map snd (ltaken_Data n lxs)) \<and>
   (t \<in> fst ` set (concat (map snd (ltaken_Data n lxs))))"
  apply (induct "(skip_n_productions_op (incr_op buf) m, lxs)" "(lgc', x, xs, lxs')" arbitrary: buf lxs lgc' lxs' m n x rule: produce_inner_alt[consumes 1])
  subgoal for h lxs' lgc' buf lgc'a lxs'a m x n'
    apply (auto split: if_splits event.splits)
    subgoal
      apply (erule prefix_production_LE.cases)
       apply auto
      apply (metis (no_types, opaque_lifting) Suc_diff_le append.assoc less_or_eq_imp_le)
      done
    subgoal
      apply (erule prefix_production_LE.cases)
       apply auto
      apply (metis (no_types, lifting) Suc_diff_le Un_iff image_Un less_or_eq_imp_le)
      done
    subgoal for wm 
      apply (erule prefix_production_LE.cases)
       apply auto
      done
    subgoal for wm 
      apply (erule prefix_production_LE.cases)
       apply auto
      done
    subgoal for t d
      apply (erule prefix_production_LE.cases)
       apply auto
      apply hypsubst_thin
      subgoal for n''
        apply (drule meta_spec[of _ "buf@d"])
        apply (drule meta_spec[of _ "0"])
        apply (drule meta_spec[of _ "n''"])
        apply (drule meta_mp)
         apply simp
        apply (drule meta_mp)
         apply simp
        apply fastforce
        done
      done
    subgoal for t d
      apply (erule prefix_production_LE.cases)
       apply auto
      apply hypsubst_thin
      subgoal for n''
        apply (drule meta_spec[of _ "buf@d"])
        apply (drule meta_spec[of _ "0"])
        apply (drule meta_spec[of _ "n''"])
        apply (drule meta_mp)
         apply simp
        apply (drule meta_mp)
         apply auto
        done
      done
    subgoal for wm 
      apply (erule prefix_production_LE.cases)
       apply auto
      subgoal for n''
        apply (drule meta_spec[of _ "buf"])
        apply (drule meta_spec[of _ "m - Suc 0"])
        apply (drule meta_spec[of _ "n''"])
        apply (drule meta_mp)
         apply simp
        apply (drule meta_mp)
         apply simp
        apply auto
        done
      done
    subgoal for wm 
      apply (erule prefix_production_LE.cases)
       apply auto
      subgoal for n''
        apply (drule meta_spec[of _ "buf"])
        apply (drule meta_spec[of _ "m - Suc 0"])
        apply (drule meta_spec[of _ "n''"])
        apply (drule meta_mp)
         apply simp
        apply (drule meta_mp)
         apply simp
        apply auto
        done
      done
    done
  subgoal for h x lxs' lgc' buf m n
    apply (erule prefix_production_LE.cases)
     apply (auto split: event.splits if_splits)
     apply (smt (verit) drop_map event.inject(1) map_eq_Cons_conv)
    apply (smt (verit, ccfv_SIG) UnI1 drop_map event.inject(1) image_Un in_set_dropD list.set_intros(1) list.set_map map_eq_Cons_conv set_remdups set_rev)
    done
  done

lemma produce_skip_n_productions_op_incr_op_soundness:
  "produce (skip_n_productions_op (incr_op buf) m) lxs = LCons (Data t data_coll) lxs' \<Longrightarrow>
   prefix_production_LE (incr_op buf) lxs (Suc m) n \<Longrightarrow>
   data_coll = buf @ concat (map snd (ltaken_Data n lxs)) \<and>
   t \<in> fst ` set (concat (map snd (ltaken_Data n lxs)))"
  apply (subst (asm) produce.code)
  apply (simp split: option.splits event.splits prod.splits)
  apply hypsubst_thin
  apply (drule produce_inner_skip_n_productions_op_incr_op)
    apply (rule refl)
   apply assumption
  apply simp
  done

lemma produce_incr_op_soundness:
  "lnth (produce (incr_op buf) lxs) m = Data t data_coll \<Longrightarrow>
   m < llength (produce (incr_op buf) lxs) \<Longrightarrow>
   prefix_production_LE (incr_op buf) lxs (Suc m) n \<Longrightarrow>
   data_coll = buf @ concat (map snd (ltaken_Data n lxs)) \<and>
   t \<in> fst ` set (concat (map snd (ltaken_Data n lxs)))"
  by (metis ldropn_Suc_conv_ldropn produce_skip_n_productions_op_incr_op_soundness produce_skip_n_productions_op_correctness)

subsection \<open>Completeness\<close> 
lemma produce_incr_op_completeness_Data:
  "lnth stream_in n = Data t batch \<Longrightarrow>
   n < llength stream_in \<Longrightarrow>
   produce (incr_op buf) stream_in = stream_out \<Longrightarrow>
   t' \<in> fst ` set batch \<Longrightarrow>
   ext = concat (map snd (ltaken_Data (Suc n) stream_in)) \<Longrightarrow>
   Data t' (buf @ ext) \<in> lset stream_out"
  apply (induct n arbitrary: stream_in buf stream_out ext)
  subgoal for buf
    apply (subst (asm) produce.code)
    apply (simp split: prod.splits option.splits)
     apply (subst (asm) produce_inner.simps)
     apply (simp split: prod.splits llist.splits list.splits)
    apply hypsubst_thin
    subgoal for x2 op x2a x x2b xs lxs'
      apply (subst (asm) produce_inner.simps)
      apply (simp split: prod.splits llist.splits list.splits)
      apply (metis (mono_tags, lifting) image_iff list.set_map set_ConsD set_remdups set_rev)
      done
    done
  subgoal for n stream_in buf stream_out ext
    apply (cases stream_in)
     apply auto[1]
    subgoal for h stream_in'
      apply (cases h)
      subgoal for t d
        apply (drule meta_spec[of _ "stream_in'"])
        apply (drule meta_spec[of _ "buf@d"])
        apply (drule meta_spec)+
        apply (drule meta_mp)
         apply simp
        apply (drule meta_mp)
         apply (metis Extended_Nat.eSuc_mono eSuc_enat llength_LCons)
        apply (drule meta_mp)
         apply (rule refl)
        apply (drule meta_mp)
         apply assumption
        apply (drule meta_mp)
         apply simp
        apply simp
        apply hypsubst_thin
        apply (subst produce.code)
        apply (simp split: prod.splits option.splits)
        apply (rule conjI)
         apply (subst produce_inner.simps)
         apply (auto split: prod.splits llist.splits event.splits list.splits)[1]
         apply (metis empty_iff lset_LNil option.exhaust prod_cases4 produce_inner_None_produce_LNil)
        apply (rule allI impI)+
        apply (subst (asm) produce_inner.simps)
        apply (auto split: prod.splits llist.splits event.splits list.splits)[1]
        done
      subgoal for wm
        apply (drule meta_spec[of _ "stream_in'"])
        apply (drule meta_spec[of _ "buf"])
        apply (drule meta_spec)+
        apply (drule meta_mp)
         apply simp
        apply (drule meta_mp)
         apply (metis Extended_Nat.eSuc_mono eSuc_enat llength_LCons)
        apply (drule meta_mp)
         apply (rule refl)
        apply (drule meta_mp)
         apply assumption
        apply (drule meta_mp)
         apply simp
        apply simp
        apply hypsubst_thin
        apply (subst produce.code)
        apply (simp split: prod.splits option.splits)
        apply (rule conjI)
         apply (subst produce_inner.simps)
         apply (auto split: prod.splits llist.splits event.splits list.splits)[1]
        apply (rule allI impI)+
        apply (subst (asm) produce_inner.simps)
        apply (auto split: prod.splits llist.splits event.splits list.splits)[1]
        done
      done
    done
  done

lemma produce_incr_op_completeness_Watermark:
  "x \<in> lset stream_in \<Longrightarrow>
   x = Watermark wm \<Longrightarrow>
   produce (incr_op buf) stream_in = stream_out \<Longrightarrow>
   Watermark wm \<in> lset stream_out"
  apply (induct stream_in arbitrary: buf stream_out wm rule: lset_induct)
  subgoal for xs buf stream_out wm
    apply simp
    apply hypsubst_thin
    apply (subst produce.code)
    apply (auto split: option.splits)  
     apply (subst produce_inner.simps)
     apply (auto split: prod.splits list.splits)
    apply (subst (asm) produce_inner.simps)
    apply (auto split: prod.splits list.splits)
    done
  subgoal for x' lxs buf stream_out wm
    apply (cases x')
    subgoal for t d
      apply simp
      apply hypsubst_thin
      apply (subst produce.code)
      apply (simp split: option.splits)
      apply (rule conjI)
      subgoal
        apply (subst produce_inner.simps)
        apply (auto split: prod.splits list.splits)
        apply (drule meta_spec[of _ buf])
        apply (subst (asm) produce.code)
        apply (auto split: option.splits)
        done
      apply (subst produce_inner.simps)
      apply (auto split: prod.splits list.splits)    
      apply (metis in_lset_shift_eq produce_inner_Some_produce set_ConsD lshift.simps(2))
      done
    subgoal for wm'
      apply simp
      apply hypsubst_thin
      apply (subst produce.code)
      apply (simp split: option.splits)
      apply (rule conjI)
      subgoal
        apply (subst produce_inner.simps)
        apply (auto split: prod.splits list.splits)
        done
      subgoal
        apply (subst produce_inner.simps)
        apply (auto split: prod.splits list.splits)
        done
      done
    done
  done

lemma produce_incr_op_completeness:
  "\<exists> wm batch . Data wm batch \<in> lset lxs \<and> t \<in> fst ` set batch \<Longrightarrow>
   monotone lxs WM \<Longrightarrow> productive lxs \<Longrightarrow>
   \<exists>batch. Data t batch \<in> lset (produce (incr_op buf) lxs)"
  apply (elim exE conjE)
  subgoal for wm batch
    apply (subst (asm) lset_conv_lnth)
    apply auto
    subgoal for b n
      using produce_incr_op_completeness_Data[where n=n and stream_in=lxs and t=wm and t'=t and batch=batch and buf=buf] apply simp
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
       apply force
      apply (drule meta_mp)
       apply (rule refl)
      apply fast
      done
    done
  done

subsection \<open>Strict monotone\<close>
lemma all_Data_strict_monotone_aux:
  "y \<in> lset lxs \<Longrightarrow> \<forall> x \<in> lset lxs . is_Data x \<and> (\<forall> wm \<in> WM . \<not> wm \<ge> tmp x) \<Longrightarrow> monotone lxs WM"
  apply (coinduction arbitrary: y lxs rule: monotone.coinduct)
  subgoal for y lxs
    apply (cases lxs)
     apply simp
    subgoal for x lxs'
      apply (cases x)
       apply simp_all
      apply (metis lset_intros(1) neq_LNil_conv monotone.LNil)
      done
    done
  done

lemma all_Data_strict_monotone:
  "\<forall> x \<in> lset lxs . is_Data x \<and> (\<forall> wm \<in> WM . \<not> wm \<ge> tmp x) \<Longrightarrow> monotone lxs WM"
  apply (cases lxs)
  using monotone.LNil apply blast
  apply (metis all_Data_strict_monotone_aux lset_intros(1))
  done

lemma produce_incr_op_strict_monotone:
  "monotone stream_in WM \<Longrightarrow>
   produce (incr_op buf) stream_in = stream_out \<Longrightarrow>
   (\<forall> n wm batch. n < llength stream_in \<longrightarrow> lnth stream_in n = Data wm batch \<longrightarrow> 
    (\<forall> t'\<in> fst ` set batch . t' \<le> wm \<and> (\<forall> wm' \<in> (WM \<union> (Watermark -` lset (ltake n stream_in))) . \<not> wm' \<ge> t'))) \<Longrightarrow>
   monotone stream_out WM"
  apply (coinduction arbitrary: stream_in WM stream_out buf rule: strict_monotone_coinduct_shift_strict_monotone_prepend_cong1)
  subgoal for stream_in WM stream_out buf
    apply (subst (asm) produce.corec.code)
    apply (subst produce.corec.code)
    apply (simp split: option.splits prod.splits)
    apply hypsubst_thin
    apply (frule produce_inner_incr_op_inversion_2)
    apply (elim exE conjE)
    apply hypsubst_thin
    subgoal premises prems for x2 lgc' x2a x xs' xs lxs buf'
      using prems(3,2,1) apply -
      apply (induct "(incr_op buf, stream_in)" "(incr_op buf', x, xs, lxs)" arbitrary: buf stream_in lxs buf' rule: produce_inner_alt)
      subgoal using prems by simp
      subgoal premises temp for h lxs' lgc' buf lxs buf'
        using temp(1,3-) apply -
        apply (subst (asm) produce_inner.simps)
        apply (simp split: llist.splits event.splits if_splits)
        subgoal for wm
          using temp(2) apply hypsubst_thin
          apply (drule meta_spec[of _ "buf"])
          apply (drule meta_spec[of _ "buf'"])
          apply (drule meta_mp)
           apply (rule refl)
          apply (drule meta_mp)
           apply (rule refl)
          apply (drule meta_mp)
           apply assumption
          apply (drule meta_mp)
          using strict_monotone_drop_head apply blast
          apply (drule meta_mp)
           apply (metis (mono_tags, lifting) Un_iff eSuc_enat ileI1 insert_iff llist.simps(19) lnth_Suc_LCons ltake_eSuc_LCons vimage_eq)
          apply auto
          done
        done
      subgoal premises p for h lxs' buf buf'
        using p apply -
        apply (frule apply_incr_op_inversion)
        apply (subst (asm) produce_inner.simps)
        apply (simp split: llist.splits event.splits if_splits)
        subgoal for t d
          apply (elim conjE disjE exE)
          apply (subgoal_tac "\<forall> x \<in> set (x#xs) . is_Data x")
           defer
           apply fastforce
          apply hypsubst_thin
          apply (rule exI[of _ "produce (incr_op buf') lxs'"])
          apply (rule exI[of _ "x # xs"])
          apply simp
          apply (rule conjI)
          subgoal 
            apply (drule sym[where t="x # xs"])
            apply (subgoal_tac "monotone (llist_of (x#xs)) WM")
             defer
            subgoal
              apply simp
              apply (rule all_Data_strict_monotone)
              apply safe
               apply force
              apply (metis (no_types, lifting) Un_iff i0_lb imageI image_insert list.simps(15) list.simps(9) lnth_0 lset_llist_of rev.simps(2) rev_rev_ident zero_enat_def)
              done
            apply auto
            done
          apply (rule conjI)
          subgoal
            apply (subst tmps_tmps)
             apply auto
            apply (metis (no_types, opaque_lifting) Un_iff enat_0 fst_conv i0_lb imageI lnth_0)
            done
          subgoal
            apply (rule monotone_prepend_cong_base)
            apply (rule exI[of _ lxs'])
            apply (rule conjI)
             apply (meson LConsData)
            apply (rule conjI)
             apply (rule exI[of _ buf'])
             apply safe
                apply (simp_all add: produce_inner_None_produce_LNil)
            using Suc_ile_eq apply fastforce
            using Suc_ile_eq apply fastforce
            apply (smt (z3) Suc_ile_eq UnCI eSuc_enat fst_conv image_eqI llist.set_intros(2) lnth_Suc_LCons ltake_eSuc_LCons vimageI)
            done
          done 
        subgoal for wm
          apply (elim conjE disjE exE)
          apply hypsubst_thin
          apply (rule exI[of _ "produce (incr_op buf') lxs'"])
          apply (rule exI[of _ "[Watermark wm]"])
          apply simp
          apply (rule conjI)
           apply (meson LConsR LConsWatermark monotone.LNil)
          apply (rule conjI)
           apply (meson LConsWatermark)
          apply (rule monotone_prepend_cong_base)
          apply (rule exI[of _ lxs'])
          apply (rule conjI)
          using LConsWatermark apply blast
          apply (rule conjI)
           apply (rule exI[of _ buf'])
           apply (simp add: produce_inner_None_produce_LNil)
          apply (erule monotone.cases)
            apply simp_all
          apply hypsubst_thin
          apply auto
             apply (metis Suc_ile_eq fst_conv imageI lnth_Suc_LCons)
          using Suc_ile_eq fst_conv imageI lnth_Suc_LCons
            apply (smt (verit, ccfv_threshold) Un_iff eSuc_enat insertI1 llist.simps(19) ltake_eSuc_LCons vimage_eq)
          using Suc_ile_eq apply fastforce
          apply (smt (verit, ccfv_threshold) Suc_ile_eq Un_iff eSuc_enat fst_conv imageI insert_iff llist.simps(19) lnth_Suc_LCons ltake_eSuc_LCons vimage_eq)
          done
        done
      done
    done
  done

subsection \<open>Productive\<close> 
lemma produce_inner_incr_op_iff_lnull:
  "(\<forall> t batch . Data t batch \<in> lset lxs \<longrightarrow> batch \<noteq> []) \<Longrightarrow>
   produce_inner (incr_op buf, lxs) = None \<longleftrightarrow> lnull lxs"
  apply (intro iffI)
  subgoal
    apply (subst (asm) produce_inner.simps)
    apply (auto split: prod.splits if_splits list.splits llist.splits event.splits)
    done
  subgoal
    apply (subst produce_inner.simps)
    apply (auto split: prod.splits if_splits list.splits llist.splits event.splits)
    done
  done

lemma llength_produce_le_produce_lxs:
  "(\<forall> t batch . Data t batch \<in> lset lxs \<longrightarrow> batch \<noteq> []) \<Longrightarrow>
   llength (produce (incr_op buf) lxs) \<le> enat n \<Longrightarrow> llength lxs \<le> n"
  apply (induct n arbitrary: buf lxs)
  subgoal 
    apply (subst (asm) produce.code)
    apply (simp add: produce_inner_incr_op_iff_lnull dual_order.order_iff_strict split: option.splits prod.splits flip: eSuc_enat)
    apply hypsubst_thin
    using zero_enat_def apply auto
    done
  subgoal for n 
    apply (subst (asm) (2) produce.code)
    apply (simp add: dual_order.order_iff_strict split: option.splits prod.splits flip: eSuc_enat)
    subgoal
      apply (subst (asm) produce_inner.simps)
      apply (simp split: prod.splits llist.splits if_splits event.splits list.splits)
      done
    subgoal for x2 x1 x2a x1a x2b x1b x2c
      apply (elim disjE)
       apply (smt (verit, best) Suc_ile_eq eSuc_enat ileI1 leD leI llength_LCons order.order_iff_strict produce_inner_Some_produce)
      apply hypsubst_thin
      subgoal
        apply (subst (asm) produce_inner.simps)
        apply (simp split: prod.splits llist.splits if_splits event.splits list.splits)
         apply hypsubst_thin
         apply (metis (no_types, lifting) enat_le_plus_same(2) llength_shift order_neq_le_trans)
        apply blast
        done
      done
    done
  done

lemma lfinite_produce_skip_n_productions_op_incr_op_not_lfinite:
  "lfinite (produce (skip_n_productions_op (incr_op buf) n) lxs) \<Longrightarrow>
  (\<forall> t batch . Data t batch \<in> lset lxs \<longrightarrow> batch \<noteq> []) \<Longrightarrow>
  \<not> lfinite lxs \<Longrightarrow> False"
  apply (induct "produce (skip_n_productions_op (incr_op buf) n) lxs" arbitrary: n rule: lfinite_induct)
  subgoal for n
    apply (subgoal_tac "llength (produce (incr_op buf) lxs) \<le> n")
     defer
     apply (simp add: produce_skip_n_productions_op_correctness)
    apply (subst (asm) produce.code)
    apply (simp split: option.splits prod.splits)
    apply (cases "produce_inner (incr_op buf, lxs)")
    subgoal
      apply (subst (asm) (2) produce_inner.simps)
      apply (simp split: prod.splits llist.splits if_splits event.splits list.splits)
      done
    subgoal for a
      apply (subst (asm) produce.code)
      apply (simp split: option.splits prod.splits)
      apply hypsubst_thin
      apply simp
      subgoal for lgc' x xs lxs'
        using llength_produce_le_produce_lxs 
        apply (metis enat_ord_code(5) llength_LCons llength_eq_infty_conv_lfinite produce_inner_Some_produce)
        done
      done
    done
  subgoal for n
    apply (drule meta_spec[of _ "Suc n"])
    apply (drule meta_mp)
     apply (simp add: produce_skip_n_productions_op_ltl_alt)
    apply (drule meta_mp)
     apply blast
    apply (drule meta_mp)
     apply blast
    apply simp
    done
  done

lemma not_lfinite_lxs_not_lfinite_produce_incr_op:
  "(\<forall> t batch . Data t batch \<in> lset lxs \<longrightarrow> batch \<noteq> []) \<Longrightarrow>
  \<not> lfinite lxs \<Longrightarrow> \<not> lfinite (produce (incr_op buf) lxs)"
  using lfinite_produce_skip_n_productions_op_incr_op_not_lfinite[where n=0] apply simp
  apply blast
  done

lemma produce_incr_op_productive:
  "productive stream_in \<Longrightarrow>
   produce (incr_op buf) stream_in = stream_out \<Longrightarrow>
   (\<forall> n wm batch. n < llength stream_in \<longrightarrow> lnth stream_in n = Data wm batch \<longrightarrow>
   (\<exists> m > n. lnth stream_in m = Watermark wm) \<and> (\<forall> t'\<in> fst ` set batch . t' \<le> wm) \<and> batch \<noteq> []) \<Longrightarrow>
   productive stream_out"
  apply (coinduction arbitrary: stream_in stream_out buf rule: productive_coinduct_prepend_cong1_shift_gen)
  subgoal for stream_in stream_out buf
    apply hypsubst_thin
    apply (subst (1 2) produce.corec.code)
    apply (simp split: option.splits prod.splits)
    apply (rule allI impI)+
    apply (frule produce_inner_incr_op_inversion_2)
    apply (elim exE conjE)
    apply simp
    apply hypsubst_thin
    subgoal premises prems for a x xs lxs buf'
      using prems(3,1,2) apply -
      apply (induct "(incr_op buf, stream_in)" arbitrary: buf stream_in lxs rule: produce_inner_alt[where y="(incr_op buf', x, xs, lxs)"])
      using prems apply simp
      subgoal premises temp for h lxs' lgc' buf'' lxs''
        using temp(1,3-) apply -
        apply (subst (asm) produce_inner.simps)
        apply (auto split: llist.splits event.splits if_splits)
        subgoal for wm
          using temp(2) apply hypsubst_thin
          apply (drule meta_spec)+
          apply (drule meta_mp)
           apply (rule refl)
          apply (drule meta_mp)
           apply simp
          apply (drule meta_mp)
           apply (meson productive_drop_head)
          apply (drule meta_mp)
          subgoal
            apply (intro allI)
            subgoal for n
              apply (drule spec[of _ "Suc n"])
              apply (fastforce simp add: Suc_ile_eq Suc_less_eq2)
              done
            done
          apply (metis (no_types, lifting))
          done
        done
      subgoal for h x' xs' lxs' lgc' buf lxs
        apply (erule productive_cases)
        subgoal for lxs''
          apply hypsubst_thin
          apply (rule disjI1)
          apply (metis lfinite_produce produce_inner_Some_lfinite_produce_lfinite)
          done
        subgoal for lxs'' t d
          apply (drule apply_incr_op_out_preserves)
          apply (elim conjE exE disjE)
          subgoal for wm' batch
            apply hypsubst_thin
            apply (subst (asm) produce_inner.simps)
            apply (simp split: llist.splits event.splits if_splits list.splits)
            apply (elim exE disjE conjE bexE)
            apply hypsubst_thin
            apply (rule disjI2)
            subgoal for t' d' wm'
              using produce_incr_op_completeness_Data
                [where n=0 and ext="d" and batch=d and t=t and t'=t' and buf=buf and stream_in="LCons (Data t d) lxs" and stream_out="(x#xs) @@- produce (incr_op buf') lxs"]
              apply -
              apply (drule meta_mp)
               apply simp
              apply (drule meta_mp)
               apply (metis enat_0 i0_lb iless_Suc_eq llength_LCons)
              apply (drule meta_mp)
              subgoal
                apply (subst produce.code)
                apply (auto split: option.splits)
                  apply (subst produce_inner.simps)
                  apply simp
                 apply (subst (asm) produce_inner.simps)
                 apply simp
                apply (subst (asm) produce_inner.simps)
                apply simp
                done
              apply (drule meta_mp)
               apply simp
              apply (drule meta_mp)
              subgoal
                apply auto
                done
              apply (rule exI[of _ "produce (incr_op buf') lxs"])
              apply (rule exI[of _ "x#xs"])
              apply (rule conjI)
               apply simp
              apply (rule conjI)
               apply (meson null_rec(1))
              subgoal
                apply (rule conjI)
                 apply blast
                apply (rule conjI)
                subgoal 
                  apply auto
                  subgoal for b zs n t'' d'
                    apply hypsubst_thin
                    apply (subgoal_tac "t'' \<in> set zs \<or> t'' = t'")
                     defer
                    subgoal premises prems
                      using prems(11,10,9,8) apply -
                      apply (induct zs arbitrary: n)
                       apply simp
                      apply auto
                      subgoal for t''' zs n
                        apply (cases n)
                         apply simp
                        subgoal for n'
                          apply (cases n')
                           apply simp
                          subgoal for n''
                            apply auto
                            done
                          done
                        done
                      done
                    apply (elim disjE)
                    subgoal
                      apply (drule spec[of _ 0])
                      apply (drule mp)
                      using i0_lb zero_enat_def apply presburger
                      apply simp
                      apply (smt (verit, best) dual_order.order_iff_strict image_iff insert_iff list.set_map list.simps(15) order.strict_trans2 produce_incr_op_completeness_Watermark rev.simps(2) set_remdups set_rev)
                      done
                    subgoal
                      apply (drule spec[of _ 0])
                      apply (drule mp)
                      using i0_lb zero_enat_def apply presburger
                      apply hypsubst_thin
                      using produce_incr_op_completeness_Watermark apply fastforce
                      done
                    done
                  subgoal for b t'' zs n t''' d'
                    apply hypsubst_thin
                    apply (subgoal_tac "t''' \<in> set zs \<or> t'' = t'''")
                     defer
                    subgoal premises prems
                      using prems(11,10,9,8) apply -
                      apply (induct zs arbitrary: n)
                       apply simp
                      apply auto
                      subgoal for t''' zs n
                        apply (cases n)
                         apply simp
                        subgoal for n'
                          apply (cases n')
                           apply simp
                          subgoal for n''
                            apply auto
                            done
                          done
                        done
                      done
                    apply (elim disjE)
                    subgoal
                      apply (drule spec[of _ 0])
                      apply (drule mp)
                      using i0_lb zero_enat_def apply presburger
                      apply simp
                      apply (smt (verit, best) dual_order.order_iff_strict image_iff insert_iff list.set_map list.simps(15) order.strict_trans2 produce_incr_op_completeness_Watermark rev.simps(2) set_remdups set_rev)
                      done
                    subgoal
                      apply (drule spec[of _ 0])
                      apply (drule mp)
                      using i0_lb zero_enat_def apply presburger
                      apply simp
                      apply hypsubst_thin
                      apply (smt (verit, best) dual_order.order_iff_strict image_iff list.set_intros(1) list.set_map order.strict_trans2 produce_incr_op_completeness_Watermark rev.simps(2) set_remdups set_rev)
                      done
                    done
                  subgoal for b t'' zs n t''' d'
                    apply hypsubst_thin
                    apply (subgoal_tac "t''' \<in> set zs \<or> t'' = t'''")
                     defer
                    subgoal premises prems
                      using prems(11,10,9,8) apply -
                      apply (induct zs arbitrary: n)
                       apply simp
                      apply auto
                      subgoal for t''' zs n
                        apply (cases n)
                         apply simp
                        subgoal for n'
                          apply (cases n')
                           apply simp
                          subgoal for n''
                            apply auto
                            done
                          done
                        done
                      done
                    apply (elim disjE)
                    subgoal
                      apply (drule spec[of _ 0])
                      apply (drule mp)
                      using i0_lb zero_enat_def apply presburger
                      apply simp
                      apply (smt (verit, best) dual_order.order_iff_strict image_iff insert_iff list.set_map list.simps(15) order.strict_trans2 produce_incr_op_completeness_Watermark rev.simps(2) set_remdups set_rev)
                      done
                    subgoal
                      apply (drule spec[of _ 0])
                      apply (drule mp)
                      using i0_lb zero_enat_def apply presburger
                      apply simp
                      apply hypsubst_thin
                      apply (smt (verit, best) dual_order.order_iff_strict image_iff list.set_intros(1) list.set_map order.strict_trans2 produce_incr_op_completeness_Watermark rev.simps(2) set_remdups set_rev)
                      done
                    done
                  done
                apply (rule conjI)
                subgoal 
                  using not_lfinite_lxs_not_lfinite_produce_incr_op apply (metis (no_types, opaque_lifting) Suc_ile_eq in_lset_conv_lnth lnth_Suc_LCons)
                  done
                apply (rule productive_prepend_cong1_base)
                apply auto
                  apply (rule exI[of _ lxs])
                  apply (intro conjI allI | assumption)+
                   apply blast
                subgoal for b zs n
                  apply (drule spec[of _ "Suc n"])
                  apply (fastforce simp add: Suc_ile_eq Suc_less_eq2)
                  done
                subgoal for b z zs
                  apply (rule exI[of _ lxs])
                  apply simp
                  apply (rule conjI)
                   apply (rule exI[of _ buf'])
                   apply simp
                  apply (intro allI impI)
                  subgoal for n wm batch
                    apply (drule spec[of _ "Suc n"])
                    apply (fastforce simp add: Suc_ile_eq Suc_less_eq2)
                    done
                  done
                subgoal for b z zs
                  apply (rule exI[of _ lxs])
                  apply simp
                  apply (rule conjI)
                   apply (rule exI[of _ buf'])
                   apply simp
                  apply (intro allI impI)
                  subgoal for n wm batch
                    apply (drule spec[of _ "Suc n"])
                    apply (fastforce simp add: Suc_ile_eq Suc_less_eq2)
                    done
                  done
                done
              done
            done
          subgoal for wm batch
            apply hypsubst_thin
            apply simp
            done
          done
        subgoal for lxs'' wm
          apply (drule apply_incr_op_out_preserves)
          apply (elim conjE exE disjE)
          subgoal for t' wma d' batch
            apply hypsubst_thin
            apply (subst (asm) produce_inner.simps)
            apply (simp split: llist.splits event.splits if_splits list.splits)
            apply fast
            done
          subgoal for t' wm' d' batch
            apply hypsubst_thin
            apply (subst (asm) produce_inner.simps)
            apply (simp split: llist.splits event.splits if_splits list.splits)
            apply (elim exE disjE conjE bexE)
            apply hypsubst_thin
            apply (rule disjI2)
            apply (rule exI[of _ "produce (incr_op buf') lxs"])
            apply (rule exI[of _ "[Watermark wm]"])
            apply (simp add: null_rec(1))
            apply (rule conjI)
            subgoal 
              apply (subst (asm) lset_conv_lnth)
              apply safe
              subgoal for n
                apply (drule spec[of _ "Suc n"])
                apply simp
                apply (drule mp)
                using Suc_ile_eq apply blast
                apply (drule spec)+
                apply (drule mp)
                 apply (drule sym[of _ "lnth lxs n"])
                 apply assumption
                apply (cases d')
                 apply simp
                subgoal for x d''
                  using produce_incr_op_completeness_Data[where n=n and stream_in=lxs and t=t' and batch=d'] apply simp
                  apply (drule meta_spec)+
                  apply (drule meta_mp)
                   apply (rule refl)
                  apply (drule meta_mp)
                   apply (rule disjI1)
                   apply (rule refl)
                  apply (drule meta_mp)
                   apply (rule refl)
                  apply auto
                  done
                done
              done
            apply (rule conjI)
            subgoal 
              using not_lfinite_lxs_not_lfinite_produce_incr_op apply (metis (no_types, opaque_lifting) Suc_ile_eq in_lset_conv_lnth lnth_Suc_LCons)
              done
            apply (rule productive_prepend_cong1_base)
            apply (rule exI[of _ lxs])
            apply (rule conjI)
             apply simp
            apply (rule conjI)
             apply (rule exI[of _ buf'])
             apply simp
            apply (intro allI)
            subgoal for n
              apply (drule spec[of _ "Suc n"])
              apply (fastforce simp add: Suc_ile_eq Suc_less_eq2)
              done
            done
          done
        done
      done
    done
  done

section \<open>multi_incr_op\<close> 
definition "multi_incr_op buf1 buf2 = compose_op (sync_op buf1) (incr_op buf2)"

subsection \<open>Strict Monotone\<close> 
lemma produce_compose_op_sync_op_incr_op_strict_monotone:
  "monotone stream_in WM \<Longrightarrow>
   productive stream_in \<Longrightarrow>
   (\<forall>x\<in>set buf1. \<forall>wm\<in>WM. \<not> fst x \<le> wm) \<Longrightarrow>
   produce (compose_op (sync_op buf1) (incr_op buf2)) stream_in = stream_out \<Longrightarrow>
   monotone stream_out WM"
  apply (subst (asm) produce_compose_op_correctness)
  apply (rule produce_incr_op_strict_monotone[where stream_in="produce (sync_op buf1) stream_in"])
  using produce_sync_op_strict_monotone apply blast
   apply assumption
  apply hypsubst_thin
  apply (rule allI)+
  apply (rule impI)+
  apply (rule ballI)+
  subgoal for n wm batch t'
    apply (rule conjI)
    using produce_sync_op_soundness
     apply (metis (no_types, opaque_lifting) in_lset_conv_lnth)
    apply (intro ballI)
    apply (erule UnE)
    subgoal for wm'
      using produce_sync_op_soundness[unfolded in_lset_conv_lnth, OF exI, OF conjI, rotated 1] apply auto
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply assumption
      apply (drule meta_mp)
       apply assumption
      apply (drule meta_mp)
       apply assumption
      apply (drule meta_mp)
       apply assumption
      apply auto
      done
    subgoal for wm'            
      using lnth_produce_skip_n_productions_op_sync_op_batch_not_ge[where i=0 and buf=buf1 and n="n" and lxs=stream_in and WM=WM and batch=batch and t=wm and wm=wm', OF refl] apply auto
      apply (metis (no_types, lifting) enat_ord_simps(2) fst_conv in_lset_conv_lnth llength_ltake lnth_ltake min_def order_less_imp_le)
      done
    done
  done

lemma produce_multi_incr_op_strict_monotone:
  "monotone stream_in WM \<Longrightarrow>
   productive stream_in \<Longrightarrow>
   (\<forall>x\<in>set buf1. \<forall>wm\<in>WM. \<not> fst x \<le> wm) \<Longrightarrow>
   produce (multi_incr_op buf1 buf2) stream_in = stream_out \<Longrightarrow>
   monotone stream_out WM"
  unfolding multi_incr_op_def produce_compose_op_correctness
  using produce_compose_op_correctness produce_compose_op_sync_op_incr_op_strict_monotone by blast

subsection \<open>Productive\<close> 
lemma produce_compose_op_sync_op_incr_op_productive:
  "productive stream_in \<Longrightarrow>
   monotone stream_in WM \<Longrightarrow>
   produce (compose_op (sync_op buf1) (incr_op buf2)) stream_in = stream_out \<Longrightarrow>
   productive stream_out"
  apply (subst (asm) produce_compose_op_correctness)
  apply (rule produce_incr_op_productive[where stream_in="produce (sync_op buf1) stream_in"])
  using produce_sync_op_productive apply blast
   apply simp
  apply (intro allI impI conjI)
  subgoal for n wm batch
    apply (metis lessI produce_skip_n_productions_op_sync_op_n_Data_Suc_n_Watermark skip_n_productions_op_0)
    done
  subgoal
    apply (metis (no_types, opaque_lifting) in_lset_conv_lnth produce_sync_op_soundness)
    done
  subgoal
    apply (metis (no_types, opaque_lifting) in_lset_conv_lnth produce_sync_op_soundness)
    done
  done

lemma produce_multi_incr_op_productive:
  "monotone stream_in WM \<Longrightarrow>
   productive stream_in \<Longrightarrow>
   (\<forall>x\<in>set buf1. \<forall>wm\<in>WM. \<not> fst x \<le> wm) \<Longrightarrow>
   produce (multi_incr_op buf1 buf2) stream_in = stream_out \<Longrightarrow>
   productive stream_out"
  unfolding multi_incr_op_def produce_compose_op_correctness
  using produce_compose_op_correctness produce_compose_op_sync_op_incr_op_productive by blast

subsection \<open>Soundness\<close> 
lemma produce_multi_incr_op_soundness:
  "lnth (produce (multi_incr_op buf1 buf2) lxs) m = Data t colld \<Longrightarrow>
   enat m < llength (produce (multi_incr_op buf1 buf2) lxs) \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   productive lxs \<Longrightarrow>
   \<exists> n . colld = 
   buf2 @ concat (map snd (ltaken_Data n (produce (sync_op buf1) lxs))) \<and>
   ts lxs t \<union> {t' \<in> fst ` set buf1 . t' \<le> t} = {t' \<in> fst ` set (concat (map snd (ltaken_Data n (produce (sync_op buf1) lxs)))). t' \<le> t} \<and>
   (\<forall> t' \<le> t. coll lxs t' + mset (coll_list buf1 t') = mset (coll_list (concat (map snd (ltaken_Data n (produce (sync_op buf1) lxs)))) t'))"
  unfolding produce_compose_op_correctness llist.set_map multi_incr_coll_mset_def multi_incr_op_def
  apply (frule lnth_produce_prefix_production_EQ_Ex)
  apply assumption
  apply (elim exE conjE)
  subgoal for n
    apply (frule produce_incr_op_soundness)
    apply assumption+
    apply (elim conjE)
    apply hypsubst_thin
    apply (rule exI[of _ "Suc n"])
    apply simp
    apply (intro conjI)
    subgoal premises prems
      using prems(3-) apply -
      apply (frule timestamp_in_taken_Data_inversion)
      apply assumption+
      apply (elim conjE exE)
      apply (subst produce_sync_op_ts_le)
      apply assumption+
      apply simp
      done
    subgoal premises prems
      using prems(3-) apply -
      apply (drule timestamp_in_taken_Data_inversion)
      apply assumption+
      apply auto
      subgoal for b wm' batch' wm t' batch bb
        using ltaken_Data_produce_soundness 
        apply (metis prems(3) prems(8) timestamp_in_taken_Data_inversion)
        done
      done
    done
  done

lemma produce_multi_incr_op_soundness_alt:
  "Data t colld \<in> lset (produce (multi_incr_op buf1 buf2) lxs)  \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   productive lxs \<Longrightarrow>
   \<exists> n . colld = 
   buf2 @ concat (map snd (ltaken_Data n (produce (sync_op buf1) lxs))) \<and>
   ts lxs t \<union> {t' \<in> fst ` set buf1 . t' \<le> t} = {t' \<in> fst ` set (concat (map snd (ltaken_Data n (produce (sync_op buf1) lxs)))). t' \<le> t} \<and>
   (\<forall> t' \<le> t. coll lxs t' + mset (coll_list buf1 t') = mset (coll_list (concat (map snd (ltaken_Data n (produce (sync_op buf1) lxs)))) t'))"
  apply (auto simp add: lset_conv_lnth)
  apply (drule sym)
  apply (drule produce_multi_incr_op_soundness)
     apply assumption+
  apply auto
  done

subsection \<open>Completeness\<close> 
lemma produce_multi_incr_op_completeness:
  "(\<exists>i d. enat i < llength lxs \<and> lnth lxs i = Data t d \<and> j = Suc i) \<or> j = 0 \<and> (\<exists>d. (t, d) \<in> set buf1) \<Longrightarrow>
    lfinite lxs \<or> (\<forall>(t', d)\<in>set buf1. \<exists>wm\<ge>t'. Watermark wm \<in> lset lxs) \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   productive lxs \<Longrightarrow>
   \<exists> batch . Data t batch \<in> lset (produce (multi_incr_op buf1 buf2) lxs) \<or> 
   (lfinite lxs \<and> (\<forall>k\<in>{j..<the_enat (llength lxs)}. \<forall>t'\<ge>t. lnth lxs k \<noteq> Watermark t'))"
  unfolding multi_incr_op_def produce_compose_op_correctness
  using 
    produce_incr_op_completeness[where lxs="produce (sync_op buf1) lxs" and WM=WM and buf=buf2]
    sync_completeness_gen_aux[where lxs=lxs and buf=buf1 and t=t and j=j and WM=WM] apply simp
  using produce_sync_op_productive produce_sync_op_strict_monotone apply blast
  done

section \<open>map_op\<close> 
primcorec map_op where
  "map_op f = Logic (\<lambda> ev. case ev of
                                Watermark wm \<Rightarrow> (map_op f, [Watermark wm])
                              | Data t d \<Rightarrow> (map_op f, [Data t (f t d)]))"

subsection \<open>Correctness\<close> 
lemma produce_map_op_correctness:
  "produce (map_op f) = lmap (\<lambda> ev . case ev of Watermark wm \<Rightarrow> Watermark wm | Data t d \<Rightarrow> Data t (f t d))"
  apply (rule ext)
  subgoal for lxs
    apply (coinduction arbitrary: lxs rule: llist.coinduct)
    apply safe
    subgoal 
      apply (subst (asm) produce.code)
      apply (auto split: option.splits event.splits)
      apply (subst (asm) (1) produce_inner.simps)
      apply (auto split: llist.splits event.splits)
      done
    subgoal 
      apply (subst (1) produce.code)
      apply (auto split: option.splits event.splits)
      apply (subst (asm) (1) produce_inner.simps)
      apply (auto split: llist.splits event.splits)
      done
    subgoal 
      apply (subst (1) produce.code)
      apply (auto split: option.splits event.splits)
         apply (simp add: produce_inner_None_produce_LNil)
        apply (subst (asm) (1) produce_inner.simps)
        apply (auto split: llist.splits event.splits)
       apply (subst (asm) (1) produce_inner.simps)
       apply (auto split: llist.splits event.splits)
      apply (subst (asm) (1) produce_inner.simps)
      apply (auto split: llist.splits event.splits)
      done
    subgoal for lxs
      apply (rule exI[of _ "ltl lxs"])
      apply auto
      apply (subst (1 2) produce.code)
      apply (auto split: option.splits)
        apply (simp add: produce_inner_None_produce_LNil)
       apply (subst (asm) (1 2) produce_inner.simps)
       apply (auto split: llist.splits event.splits)
        apply (subst produce.code)
        apply (subst produce_inner.simps)
        apply (auto split: llist.splits event.splits)
       apply (subst produce.code)
       apply (subst produce_inner.simps)
       apply (auto split: llist.splits event.splits)
      apply (subst (asm) (1 2) produce_inner.simps)
      apply (auto split: llist.splits event.splits)
      subgoal
        apply (subst produce.code)
        apply (subst produce_inner.simps)
        apply (auto split: llist.splits event.splits)
        done
        apply (subst produce.code)
        apply (subst produce_inner.simps)
        apply (auto split: llist.splits event.splits)
       apply (subst produce.code)
       apply (subst produce_inner.simps)
       apply (auto split: llist.splits event.splits)
      apply (subst produce.code)
      apply (subst produce_inner.simps)
      apply (auto split: llist.splits event.splits)
      done
    done
  done

subsection \<open>Strict monotone\<close> 
lemma produce_map_op_strict_monotone:
  "monotone stream_in WM \<Longrightarrow>
   produce (map_op f) stream_in = stream_out \<Longrightarrow>
   monotone stream_out WM"
  unfolding produce_map_op_correctness
  apply simp
  apply hypsubst_thin
  apply (coinduction arbitrary: WM f stream_in  rule: monotone.coinduct)
  apply (erule monotone.cases)
    apply auto
  done

subsection \<open>Productive\<close> 
lemma produce_map_op_strict_productive:
  "productive stream_in \<Longrightarrow>
   produce (map_op f) stream_in = stream_out \<Longrightarrow>
   productive stream_out"
  unfolding produce_map_op_correctness productive_alt
  apply simp
  apply hypsubst_thin
  apply (coinduction arbitrary: f stream_in rule: productive'.coinduct)
  apply (erule productive'.cases)
    apply force+
  done

lemma lconcat_lmap_LNil:
  "\<forall> x \<in> lset lxs . f x = LNil \<Longrightarrow>
   lconcat (lmap f lxs) = LNil"
  apply (auto simp add: lconcat_eq_LNil)
  done

(* FIXME: move me *)
lemma produce_inner_aux:
  "produce_inner (skip_n_productions_op op n, lxs) = None \<Longrightarrow>
   llength (produce op lxs) \<le> n"
  by (metis ldropn_eq_LNil produce_inner_None_produce_LNil produce_skip_n_productions_op_correctness)

corecursive lconcat where
  "lconcat xss = (if \<forall>xs \<in> lset xss. xs = [] then LNil else case xss of LNil \<Rightarrow> LNil
     | LCons [] xss' \<Rightarrow> lconcat xss'
     | LCons (x # xs) xss' \<Rightarrow> LCons x (lshift xs (lconcat xss')))"
  by (relation "measure (\<lambda>xss. LEAST i. lnth xss i \<noteq> [])")
    (auto simp: lset_conv_lnth Least_Suc)

lemma lconcat_unique:
  assumes "\<And>xss. f xss = (if \<forall>xs\<in>lset xss. xs = [] then LNil else case xss of LNil \<Rightarrow> LNil
     | LCons [] xss' \<Rightarrow> f xss'
     | LCons (x # xs) xss' \<Rightarrow> LCons x (lshift xs (f xss')))"
  shows "f = lconcat"
proof(rule ext)
  show "f xss = lconcat xss" for xss
  proof(coinduction arbitrary: xss rule: llist.coinduct_upto)
    case (Eq_llist xss)
    show ?case
      apply(induction xss rule: lconcat.inner_induct)
      apply(subst (1 2 3 5) assms)
      apply(subst (1 2 3 5) lconcat.code)
      apply (auto split: llist.splits list.splits intro: llist.cong_intros)
      done
  qed
qed

lemma lconcat_all_Nil: "\<forall>xs\<in>lset xss. xs = [] \<Longrightarrow> lconcat xss = LNil"
  by (subst lconcat.code) (auto)

lemma lconcat_code:
  "lconcat xss = (case xss of LNil \<Rightarrow> LNil | LCons xs xss' \<Rightarrow> lshift xs (lconcat xss'))"
  apply (rule lconcat_unique[THEN sym, THEN fun_cong])
  apply (subst lconcat.code)
  apply (auto simp: lconcat_all_Nil split: llist.splits list.splits)
  done

section \<open>flatten_op\<close> 
primcorec flatten_op where
  "flatten_op = Logic (\<lambda> ev. case ev of
                                Watermark wm \<Rightarrow> (flatten_op, [Watermark wm])
                            | Data t d \<Rightarrow> (flatten_op, map (Data t) d))"


lemma produce_flatten_op_correctness_aux:
  "\<forall> t d . Data t d \<in> lset lxs \<and> d \<noteq> [] \<Longrightarrow>
   produce flatten_op lxs = lconcat (lmap (\<lambda> ev . case ev of Watermark wm \<Rightarrow> [Watermark wm] | Data t d \<Rightarrow> map (Data t) d) lxs)"
     apply (auto split: option.splits)
  done

lemma produce_inner_flatten_op_None_Data_False:
  "Data t d \<in> lset lxs \<Longrightarrow> d \<noteq> [] \<Longrightarrow> produce_inner (flatten_op, lxs) = None \<Longrightarrow> False"
  apply (induct lxs rule: lset_induct)
    apply (subst (asm) produce_inner.simps)
    apply (auto split: event.splits list.splits)
    apply (subst (asm) produce_inner.simps)
  apply (auto split: event.splits list.splits)
  done

lemma produce_inner_flatten_op_None_False:
  "Watermark wm \<in> lset lxs \<Longrightarrow> produce_inner (flatten_op, lxs) = None \<Longrightarrow> False"
  apply (induct lxs rule: lset_induct)
    apply (subst (asm) produce_inner.simps)
    apply (auto split: event.splits list.splits)
    apply (subst (asm) produce_inner.simps)
  apply (auto split: event.splits list.splits)
  done

lemma produce_inner_flatten_op_None_f_empty_aux:
  "Data t d \<in> lset lxs \<Longrightarrow> produce_inner (flatten_op, lxs) = None \<Longrightarrow> d = []"
  apply (induct lxs rule: lset_induct)
   apply (subst (asm) produce_inner.simps)
   apply (auto split: list.splits)
   apply (subst (asm) (2) produce_inner.simps)
   apply (auto split: list.splits event.splits)
  done

lemma produce_inner_flatten_op_None_f_empty:
  "produce_inner (flatten_op, lxs) = None \<Longrightarrow>
   \<forall> t d . Data t d \<in> lset lxs \<longrightarrow> d = []"
  apply safe
  apply (meson produce_inner_flatten_op_None_f_empty_aux)
  done

lemma produce_inner_flatten_op_None_no_Watermark:
  "produce_inner (flatten_op, lxs) = None \<Longrightarrow>
   \<not> (\<exists> wm . Watermark wm \<in> lset lxs)"
  unfolding not_def
  apply safe
  using produce_inner_flatten_op_None_False apply blast
  done

lemma produce_inner_flatten_op_Some_flatten_op_None:
  "produce_inner op_lxs = Some (op, x, xs, lxs') \<Longrightarrow>
   op_lxs = (flatten_op, lfilter (\<lambda>x. case x of Data t d \<Rightarrow> d \<noteq> [] | Watermark x \<Rightarrow> True) lxs) \<Longrightarrow>
   produce_inner (flatten_op, lxs) = None \<Longrightarrow>
   False"
  apply (induct op_lxs "(op, x, xs, lxs')" arbitrary: lxs op x xs lxs' rule: produce_inner_alt[consumes 1])
  subgoal for op h lxs' lgc' op' x xs lxs'a lxs
    apply (auto split: if_splits event.splits; hypsubst_thin)
    apply (metis (mono_tags, lifting) lfilter_id_conv lfilter_idem llist.set_intros(1))
    done
  subgoal for op h x xs lxs' lgc' lxs
    apply (auto split: if_splits event.splits; hypsubst_thin)
    apply (metis (mono_tags, lifting) llist.set_intros(1) lset_lfilter mem_Collect_eq produce_inner_flatten_op_None_f_empty)
    apply (metis (no_types, lifting) llist.set_intros(1) lset_lfilter mem_Collect_eq produce_inner_flatten_op_None_False)
    done
  done

lemma produce_inner_flatten_op_Some_Some_ex:
  "produce_inner oo = Some (op, x, xs, lxs') \<Longrightarrow>
   oo = (flatten_op, lxs) \<Longrightarrow>
  \<exists> lxs'' . produce_inner (flatten_op, lfilter (\<lambda>x. case x of Data t d \<Rightarrow> d \<noteq> [] | Watermark x \<Rightarrow> True) lxs) = Some (flatten_op, x, xs, lxs'')"
  apply (induct oo "(op, x, xs, lxs')" arbitrary: lxs op x xs lxs' rule: produce_inner_alt[consumes 1])
  subgoal 
    apply (auto split: if_splits event.splits; hypsubst_thin)
    apply (smt (verit, del_insts) lfilter_cong)
    done
  subgoal for op h x xs lxs' lgc' lxs
    apply (auto split: if_splits event.splits; hypsubst_thin)
     apply (subst produce_inner.simps)
    apply (auto split: if_splits event.splits prod.splits llist.splits; hypsubst_thin)
     apply (subst produce_inner.simps)
    apply (auto split: if_splits event.splits prod.splits llist.splits; hypsubst_thin)
    done
  done

lemma produce_inner_None_constant_op:
  "ev \<in> lset lxs \<Longrightarrow> \<forall>ev. fst (apply op ev) = op \<Longrightarrow> produce_inner (op, lxs) = None \<Longrightarrow> snd (apply op ev) = []"
  apply (induct lxs rule: lset_induct)
   apply (subst (asm) produce_inner.simps)
   apply (auto split: list.splits prod.splits list.splits)
     apply (subst (asm) produce_inner.simps)
   apply (auto split: list.splits prod.splits list.splits)
  apply (metis fst_conv)
  done

lemma produce_inner_Some_constant_op:
  "produce_inner (op, lxs) = Some (op', x, xs, lxs') \<Longrightarrow> \<forall>ev. fst (apply op ev) = op \<Longrightarrow> 
   (\<lambda>ev. llist_of (snd (apply op ev))) ` lset lxs \<subseteq> Collect lnull \<Longrightarrow> False"
    apply (induct "(op, lxs)" "(op', x, xs, lxs')" arbitrary: lxs op x xs lxs' rule: produce_inner_alt[consumes 1])
   apply (auto split: list.splits prod.splits list.splits)
  apply (metis fst_conv)
  done

lemma flatten_op_Nil[simp]:
  "snd (apply flatten_op (Data t [])) = []"
   apply (auto split: list.splits)
  done

lemma lconcat_lmap_LNil':
  "\<forall>t d. Data t d \<in> lset lxs \<longrightarrow> d = [] \<Longrightarrow> \<nexists>wm. Watermark wm \<in> lset lxs \<Longrightarrow>
   lconcat (lmap (case_event (\<lambda>t. map (Data t)) (\<lambda>wm. [Watermark wm])) lxs) = LNil"
  apply (rule lconcat_all_Nil)
  apply (auto split: event.splits)
  done


lemma produce_inner_flatten_op_None_le_Suc_n:
  "produce_inner oo = Some (op', x, xs, lxs') \<Longrightarrow>
   oo = (skip_n_productions_op flatten_op n, lxs) \<Longrightarrow>
   produce_inner (skip_n_productions_op flatten_op (Suc n), lxs) = None \<Longrightarrow>
   llength (lconcat (lmap (\<lambda>z. case z of Data t d \<Rightarrow> (map (Data t) d) | Watermark wm \<Rightarrow> [Watermark wm]) lxs)) \<le> enat (Suc n)"
    apply (induct oo "(op', x, xs, lxs')" arbitrary: n lxs x xs lxs' op' rule: produce_inner_alt[consumes 1])
  subgoal 
    apply (auto split: option.splits event.splits if_splits; hypsubst_thin)
    subgoal 
   apply (subst (asm) (2) produce_inner.simps)
    apply (auto split: option.splits event.splits if_splits)
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
    apply (simp add: Suc_diff_le)
      apply (subst lconcat.corec.code)
      apply (auto split: list.splits event.splits)
          using enat_ile enat_ord_simps(1) less_SucI less_imp_le_nat plus_enat_simps(1) 
  apply (smt (verit, ccfv_threshold) Suc_diff_Suc Zero_neq_Suc diff_is_0_eq eSuc_enat eSuc_ile_mono enat_llength_ldropn length_Cons length_map lessI linordered_semidom_class.add_diff_inverse llength_shift nle_le shift_eq_shift_ldropn_length)
          using enat_ile enat_ord_simps(1) less_SucI less_imp_le_nat plus_enat_simps(1) 
          apply (smt (verit, ccfv_threshold) Suc_diff_Suc Zero_neq_Suc diff_is_0_eq eSuc_enat eSuc_ile_mono enat_llength_ldropn length_Cons length_map lessI linordered_semidom_class.add_diff_inverse llength_shift nle_le shift_eq_shift_ldropn_length)
      done
    subgoal
  apply (subst (asm) (2) produce_inner.simps)
    apply (auto split: option.splits event.splits if_splits)
      apply (drule meta_spec[of _ 0])
      apply (drule meta_mp)
      apply simp
      apply (drule meta_mp)
       apply (simp add: Suc_diff_le)
  apply (subst lconcat.corec.code)
      apply (auto split: list.splits event.splits)
          using enat_ile enat_ord_simps(1) less_SucI less_imp_le_nat plus_enat_simps(1) 
  apply (smt (verit, ccfv_threshold) Suc_diff_Suc Zero_neq_Suc diff_is_0_eq eSuc_enat eSuc_ile_mono enat_llength_ldropn length_Cons length_map lessI linordered_semidom_class.add_diff_inverse llength_shift nle_le shift_eq_shift_ldropn_length)
          using enat_ile enat_ord_simps(1) less_SucI less_imp_le_nat plus_enat_simps(1) 
          apply (smt (verit, ccfv_threshold) Suc_diff_Suc Zero_neq_Suc diff_is_0_eq eSuc_enat eSuc_ile_mono enat_llength_ldropn length_Cons length_map lessI linordered_semidom_class.add_diff_inverse llength_shift nle_le shift_eq_shift_ldropn_length)
      done
    subgoal 
   apply (subst (asm) (2) produce_inner.simps)
    apply (auto split: option.splits event.splits if_splits)
      apply (drule meta_spec)+
      apply (drule meta_mp)
       apply (rule refl)
      apply (drule meta_mp)
    apply (simp add: Suc_diff_le)
  apply (subst lconcat.corec.code)
      apply (auto split: list.splits event.splits)
          using enat_ile enat_ord_simps(1) less_SucI less_imp_le_nat plus_enat_simps(1) 
  apply (smt (verit, ccfv_threshold) Suc_diff_Suc Zero_neq_Suc diff_is_0_eq eSuc_enat eSuc_ile_mono enat_llength_ldropn length_Cons length_map lessI linordered_semidom_class.add_diff_inverse llength_shift nle_le shift_eq_shift_ldropn_length)
      done
    subgoal 
   apply (subst (asm) (2) produce_inner.simps)
    apply (auto split: option.splits event.splits if_splits)
      apply (drule meta_spec[of _ 0])
      apply (drule meta_mp)
      apply simp
      apply (drule meta_mp)
       apply (simp add: Suc_diff_le)
  apply (subst lconcat.corec.code)
      apply (auto split: list.splits event.splits)
          using enat_ile enat_ord_simps(1) less_SucI less_imp_le_nat plus_enat_simps(1) 
  apply (smt (verit, ccfv_threshold) Suc_diff_Suc Zero_neq_Suc diff_is_0_eq eSuc_enat eSuc_ile_mono enat_llength_ldropn length_Cons length_map lessI linordered_semidom_class.add_diff_inverse llength_shift nle_le shift_eq_shift_ldropn_length)
      done
    done
  subgoal for op h x xs lxs' lgc' n lxs
  apply (auto split: option.splits event.splits if_splits)
  subgoal for t d
   apply (subst (asm) produce_inner.simps)
    apply (auto split: list.splits if_splits event.splits)
    apply hypsubst_thin
  apply (subst lconcat_code)
    apply (auto split: llist.splits list.splits event.splits)
    using lconcat_lmap_LNil' 
    apply (metis Orderings.order_eq_iff length_map llength_llist_of produce_inner_flatten_op_None_False produce_inner_flatten_op_None_f_empty shift_LNil) 
    done
  subgoal for wm
   apply (subst (asm) produce_inner.simps)
    apply (auto split: list.splits if_splits event.splits)
    apply hypsubst_thin
  apply (subst lconcat_code)
    apply (auto split: llist.splits list.splits event.splits)
    using lconcat_lmap_LNil' 
    apply (metis dual_order.refl eSuc_enat enat_0 llength_LNil produce_inner_flatten_op_None_False produce_inner_flatten_op_None_f_empty)
    done
  done
  done
  

lemma produce_inner_skip_n_productions_op_None_le_n:
  "produce_inner (skip_n_productions_op flatten_op n, lxs) = None \<Longrightarrow>
   llength (lconcat (lmap (\<lambda>z. case z of Data t d \<Rightarrow> map (Data t) d | Watermark wm \<Rightarrow> [Watermark wm]) lxs)) \<le> n"
  apply (induct n arbitrary: lxs)
  subgoal 
    apply simp
    apply (simp add: lconcat_lmap_LNil' produce_inner_flatten_op_None_f_empty produce_inner_flatten_op_None_no_Watermark)
     done
  subgoal for n lxs
    apply (cases "produce_inner (skip_n_productions_op flatten_op n, lxs)")
    subgoal
      using Suc_ile_eq order.order_iff_strict 
      apply (metis (no_types, lifting) verit_comp_simplify1(3))
      done
    subgoal for y
      apply (cases y)
      apply hypsubst_thin
      using produce_inner_flatten_op_None_le_Suc_n apply blast
      done
    done
  done

lemma produce_inner_flatten_op_Some_le:
  "produce_inner oo = Some (op', x, xs, lxs') \<Longrightarrow>
   oo = (skip_n_productions_op flatten_op n, lxs) \<Longrightarrow>
   llength (lconcat (lmap (\<lambda>z. case z of Data t d \<Rightarrow> map (Data t) d | Watermark wm \<Rightarrow> [Watermark wm]) lxs)) \<le> enat n \<Longrightarrow> False"
  apply (induct oo "(op', x, xs, lxs')" arbitrary: n lxs x xs lxs' op' rule: produce_inner_alt[consumes 1])
  subgoal 
    apply (auto split: if_splits event.splits)
       apply (subst (asm) (2) lconcat_code)
       apply (auto split: llist.splits list.splits event.splits)
       apply (metis (no_types, lifting) LNil_eq_shift_iff ldropn_eq_LNil ldropn_shift length_map)
      apply (subst (asm) (2) lconcat_code)
      apply (auto split: llist.splits list.splits event.splits)
      apply (metis (no_types, lifting) One_nat_def co.enat.sel(2) eSuc_le_iff epred_enat)
     apply (subst (asm) (2) lconcat_code)
     apply (auto split: llist.splits list.splits event.splits)
     apply (metis (no_types, lifting) dual_order.refl ldropn_eq_LNil length_Cons length_map less_Suc_eq llength_LNil shift_eq_shift_ldropn_length skip_n_productions_op_0 zero_enat_def)
    apply (subst (asm) (2) lconcat_code)
    apply (auto split: llist.splits list.splits event.splits)
    apply (metis One_nat_def eSuc_ile_mono enat_0 one_eSuc one_enat_def skip_n_productions_op_0)
    done
  subgoal for op h x xs lxs' lgc' n lxs
    apply (auto split: if_splits event.splits)
     apply (subst (asm) lconcat_code)
     apply (auto split: llist.splits list.splits event.splits)
     apply (metis drop_eq_Nil2 enat_less_enat_plusI leD leI list.distinct(1) llength_shift)
    apply (subst (asm) lconcat_code)
    apply (auto split: llist.splits list.splits event.splits)
    apply (metis drop_Cons' drop_Nil enat_0 list.distinct(1) not_eSuc_ilei0)
    done
  done

lemma produce_inner_skip_n_productions_op_Some_lhd:
  "produce_inner oo = Some (op', x, xs, lxs') \<Longrightarrow>
   oo = (skip_n_productions_op flatten_op n, lxs) \<Longrightarrow>
   x = lhd (ldropn n (lconcat (lmap (\<lambda>z. case z of Data t d \<Rightarrow> map (Data t) d | Watermark wm \<Rightarrow> [Watermark wm]) lxs)))"
  apply (induct oo "(op', x, xs, lxs')" arbitrary: n lxs x xs lxs' op' rule: produce_inner_alt[consumes 1])
  subgoal for op h lxs' lgc' x xs lxs'a op' n lxs
    apply (auto simp add: lappend_llist_of ldropn_shift split: if_splits event.splits; hypsubst_thin)
    apply (subst (2) lconcat_code)
       apply (auto simp add: ldropn_shift split: llist.splits list.splits event.splits)
    apply (subst (2) lconcat_code)
      apply (auto simp add: ldropn_shift split: llist.splits list.splits event.splits)
    apply (metis Suc_lessD diff_Suc_Suc gr0_conv_Suc ldropn_Suc_LCons minus_nat.diff_0)
    apply (subst lconcat_code)
     apply (auto simp add: ldropn_shift split: llist.splits list.splits event.splits)
     apply (metis ldropn_0 skip_n_productions_op_0)
    apply (subst lconcat_code)
    apply (auto simp add: ldropn_shift split: llist.splits list.splits event.splits)
    apply (metis ldropn_0 skip_n_productions_op_0)
    done
  subgoal for op h x xs lxs' lgc' n lxs
    apply (auto split: if_splits event.splits; hypsubst_thin)
     apply (subst lconcat_code)
     apply (auto simp add: ldropn_shift split: llist.splits list.splits event.splits)
     apply (subst lconcat_code)
    apply (auto simp add: ldropn_shift split: llist.splits list.splits event.splits)
    apply (metis drop_Cons' drop_Nil eq_LConsD ldropn_0 list.distinct(1) nth_Cons_0)
    done
  done

lemma produce_flatten_op_skip_n_productions_op_correctness:
  "produce (skip_n_productions_op flatten_op n) lxs = ldropn n (lconcat (lmap (\<lambda> ev . case ev of Watermark wm \<Rightarrow> [Watermark wm] | Data t d \<Rightarrow> map (Data t) d) lxs))"
  apply (coinduction arbitrary: lxs n rule: llist.coinduct)
 apply (intro impI conjI)
  subgoal for lxs
    apply (subst produce.code)
    apply (auto split: option.splits)
    using produce_inner_skip_n_productions_op_None_le_n apply blast
    using  produce_inner_flatten_op_Some_le apply blast
    done
  subgoal for lxs n
    apply (subst produce.code)
    apply (auto split: option.splits)
    using produce_inner_skip_n_productions_op_None_le_n apply blast
    subgoal for op' x xs lxs'
      using produce_inner_skip_n_productions_op_Some_lhd apply fast
      done
    done
  subgoal for lxs n
    apply (rule exI[of _ lxs])
    apply (rule exI[of _ "Suc n"])
    apply auto
    apply (metis produce_skip_n_productions_op_ltl_alt)
    apply (simp add: ldrop_eSuc_ltl ltl_ldropn)
    done
  done

lemma produce_flatten_op_correctness:
  "produce flatten_op lxs = lconcat (lmap (\<lambda> ev . case ev of Watermark wm \<Rightarrow> [Watermark wm] | Data t d \<Rightarrow> map (Data t) d) lxs)"
  using produce_flatten_op_skip_n_productions_op_correctness[where n=0] apply auto
  done

lemma singleton_lshift:
  "[x] @@- lxs = LCons x lxs"
  apply simp
  done

lemma monotone_map:
  "\<forall> wm \<in> WM . \<not> wm \<ge> t \<Longrightarrow> monotone (llist_of (map (Data t) xs)) WM"
  apply (induct xs arbitrary: t WM)
  apply simp
  using monotone.LNil apply blast
  apply (simp add: LConsL)
  done


lemma produce_inner_flatten_op_monotone:
  "produce_inner oo = Some (op, x, xs, lxs') \<Longrightarrow>
   oo = (flatten_op, lxs) \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   monotone (LCons x (llist_of xs)) WM"
  apply (induct oo "(op, x, xs, lxs')" arbitrary: lxs x xs lxs' op WM rule: produce_inner_alt[consumes 1])
  subgoal 
    apply (auto split: event.splits)
    using strict_monotone_drop_head apply blast
    done
  apply (auto split: event.splits)
    using monotone_map apply (metis LConsData LConsL)
  apply (meson LConsWatermark monotone.LNil strict_monotone_with_smaller_initial_watermark_Watermark)
    done

lemma wms_monotone_llist_of_not_ge:
  "wm \<in> wms xs \<Longrightarrow> wm' \<in> WM \<Longrightarrow> monotone (llist_of xs) WM \<Longrightarrow> \<not> wm \<le> wm'"
  apply (induct xs arbitrary: wm wm' WM)
   apply simp
  subgoal for a xs wm wm' WM
    apply (cases a)
     apply simp
    using strict_monotone_drop_head apply blast
    apply auto
     apply (meson LConsWatermark)
    using strict_monotone_drop_head apply blast
    done
  done

lemma tmps_monotone_llist_of_not_ge:
  "wm \<in> tmps xs \<Longrightarrow> wm' \<in> WM \<Longrightarrow> monotone (llist_of xs) WM \<Longrightarrow> \<not> wm \<le> wm'"
  apply (induct xs arbitrary: wm wm' WM)
   apply simp
  subgoal for a xs wm wm' WM
    apply (cases a)
     apply simp
     apply auto
      apply (smt (verit, best) LConsData)
    using strict_monotone_drop_head apply blast
    using strict_monotone_drop_head apply blast
    done
  done

lemma produce_inner_flatten_constant:
  "produce_inner oo = Some (op, x, xs, lxs') \<Longrightarrow> 
   oo = (flatten_op, lxs) \<Longrightarrow>
   op = flatten_op"
  apply (induct oo "(op, x, xs, lxs')" arbitrary: lxs x xs lxs' op WM rule: produce_inner_alt[consumes 1])
    apply (auto split: event.splits)
  done

lemma produce_inner_flatten_monotone:
  "produce_inner oo = Some (op, x, xs, lxs') \<Longrightarrow> 
   oo = (flatten_op, lxs) \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   monotone lxs' (wms (x # xs) \<union> WM)"
  apply (induct oo "(op, x, xs, lxs')" arbitrary: lxs x xs lxs' op WM rule: produce_inner_alt[consumes 1])
  subgoal 
    apply (auto split: event.splits)
    using strict_monotone_drop_head apply blast
    done
  subgoal for op h x xs lxs' lgc' lxs WM
    apply (auto split: event.splits)
    using strict_monotone_drop_head apply blast
    using strict_monotone_LCons_Watermark_insert apply blast
    done
  done

subsection \<open>Strict monotone\<close> 
lemma produce_flatten_op_strict_monotone:
  "monotone stream_in WM \<Longrightarrow>
   produce flatten_op stream_in = stream_out \<Longrightarrow>
   monotone stream_out WM"
  unfolding produce_flatten_op_correctness
  apply hypsubst_thin
  apply (coinduction arbitrary: WM stream_in rule: strict_monotone_coinduct_shift_strict_monotone_prepend_cong1)
  apply (erule monotone.cases)
    apply (simp add: lconcat_code)
  subgoal for WM stream_in WM' wm lxs
    apply hypsubst_thin
    apply (rule disjI2)
    apply (rule exI[of _ "WM'"])
    apply (rule exI[of _ "lconcat (lmap (case_event (\<lambda>t d. map (Data t) d) (\<lambda>wm. [Watermark wm])) lxs)"])
    apply (rule exI[of _ "[Watermark wm]"])
    apply simp
    apply safe
      apply (subst lconcat_code)
    apply auto
     apply (meson LConsR monotone.LNil )
    apply (metis (mono_tags, lifting) monotone_prepend_cong_base)
    done
  subgoal for WM stream_in WM' t xs d
    apply hypsubst_thin
    unfolding produce_flatten_op_correctness[symmetric]
    apply (subst (1 2) produce.code)
    apply (auto split: option.splits)
    subgoal for op x xs' lxs'
      apply (rule exI[of _ "produce op lxs'"])
      apply (rule exI[of _ "x#xs'"])
      apply (subst (asm) produce_inner.simps)
      apply (simp split: list.splits)
      subgoal
        apply safe
        using produce_inner_flatten_op_monotone apply blast
          apply hypsubst_thin
        subgoal for wm'
          apply (drule produce_inner_flatten_op_monotone)
          apply (rule refl)
          apply assumption
          using wms_monotone_llist_of_not_ge apply force
          done
        subgoal for wm'
          apply (drule produce_inner_flatten_op_monotone)
          apply (rule refl)
          apply assumption
          using tmps_monotone_llist_of_not_ge apply force
          done
      apply (rule monotone_prepend_cong_base)
        subgoal 
          apply (rule exI[of _ lxs'])
          apply auto
            using produce_inner_flatten_constant apply blast
            using produce_inner_flatten_monotone apply blast
            done
          done
        subgoal
        apply safe
             apply (simp add: LConsL monotone_map)+
          apply (meson monotone_map tmps_monotone_llist_of_not_ge)
           apply (rule monotone_prepend_cong_base)
        subgoal 
          apply (rule exI[of _ lxs'])
          apply auto
          done
        done
      done
    done
  done

section \<open>union_op\<close> 
primcorec union_op :: "'t set \<Rightarrow> (('t::order, 'b) event, ('t + 't, 'b) event) op" where
  "union_op W = Logic (\<lambda> ev. case ev of
      Data tt d \<Rightarrow>
        let t = (case tt of Inl x \<Rightarrow> x | Inr x \<Rightarrow> x) in
        (union_op W, [Data t d])
    | Watermark tt \<Rightarrow>
        let t = (case tt of Inl x \<Rightarrow> x | Inr x \<Rightarrow> x) in
        if t \<in> W then (union_op (W - {t}), [Watermark t])
        else (union_op (W \<union> {t}), []))"

subsection \<open>Soundness\<close> 
lemma produce_inner_union_op_Data:
  "produce_inner op_lxs = Some (lgc', x::('t::order, 'b) event, xs, lzs) \<Longrightarrow>
   op_lxs = (union_op W, lxs) \<Longrightarrow>
   x = Data t d \<Longrightarrow>
   Data (Inl t) d \<in> lset lxs \<or> Data (Inr t) d \<in> lset lxs"
  apply (induct op_lxs "(lgc', x, xs, lzs)" arbitrary: W lxs lgc' rule: produce_inner_alt[consumes 1])
   apply (auto split: event.splits if_splits sum.splits)
  done

lemma produce_inner_skip_n_productions_op_union_op_Data:
  "produce_inner op_lxs = Some (lgc', x::('t::order, 'b) event, xs, lzs) \<Longrightarrow>
   op_lxs = (skip_n_productions_op (union_op W) n, lxs) \<Longrightarrow>
   x = Data t d \<Longrightarrow>
   Data (Inl t) d \<in> lset lxs \<or> Data (Inr t) d \<in> lset lxs"
  apply (induct op_lxs "(lgc', x, xs, lzs)" arbitrary: n W lxs lgc' rule: produce_inner_alt[consumes 1])
   apply (auto split: event.splits if_splits sum.splits)
  apply (metis (mono_tags) skip_n_productions_op_0)+
  apply (metis Suc_lessI bot_nat_0.not_eq_extremum drop0 drop_Suc_Cons event.inject(1) list.discI nth_Cons_0)
  apply (metis drop_Cons' drop_Nil event.inject(1) list.inject list.sel(3) not_Cons_self tl_drop)
  apply (metis drop_Cons' drop_Nil event.inject(1) list.distinct(1) list.inject)
  apply (metis drop_Cons' drop_Nil event.inject(1) list.inject list.simps(3))
  apply (metis drop_Cons' drop_Nil event.distinct(1) list.discI nth_Cons_0)
  apply (metis drop_Cons' drop_Nil event.distinct(1) list.discI nth_Cons_0)
  done


lemma produce_inner_union_op_singleton:
  "produce_inner op_lxs = Some (lgc', x::('t::order, 'b) event, xs, lzs) \<Longrightarrow>
   op_lxs = (union_op W, lxs) \<Longrightarrow>
   xs = []"
  apply (induct op_lxs "(lgc', x, xs, lzs)" arbitrary: W lxs lgc' rule: produce_inner_alt[consumes 1])
   apply (auto split: event.splits if_splits sum.splits)
  done

lemma skip_n_productions_op_union_op_Data_soundness:
  "produce (skip_n_productions_op (union_op W) n) lxs = LCons (Data t d) lzs \<Longrightarrow> 
   Data (Inl t) d \<in> lset lxs \<or> Data (Inr t) d \<in> lset lxs"
  apply (subst (asm) produce.code)
  apply (simp split: option.splits prod.splits; hypsubst_thin)
  apply (simp add: produce_inner_skip_n_productions_op_union_op_Data)
  done

lemma union_op_Data_soundness:
  "Data t d \<in> lset (produce (union_op W) lxs) \<Longrightarrow> 
   Data (Inl t) d \<in> lset lxs \<or> Data (Inr t) d \<in> lset lxs"
  apply (subst (asm) lset_conv_lnth)
  apply simp
  apply (elim exE conjE)
  subgoal for n
    apply (rule skip_n_productions_op_union_op_Data_soundness[where n=n and W=W and lzs="ldropn (Suc n) (produce (union_op W) lxs)"])
    apply (subst produce_skip_n_productions_op_correctness)
    apply (metis ldropn_Suc_conv_ldropn)
    done
  done

subsection \<open>Completness\<close> 
lemma produce_union_op_Inl_completeness:
  "Data (Inl t) d \<in> lset lxs \<Longrightarrow>
   Data t d \<in> lset (produce (union_op W) lxs)"
  apply (subst (asm) lset_conv_lnth)
  apply safe
  subgoal for n
    apply (induct n arbitrary: t d lxs W)
    subgoal for t d lxs
      apply (subst produce.code)
      apply (auto split: option.splits)
      subgoal
        apply (cases lxs)
         apply simp_all
        apply (subst produce_inner.simps)
        apply auto
        done
      subgoal for op y ys lys
        apply (cases lxs)
         apply simp_all
        subgoal for x lxs'
          apply hypsubst_thin
          apply (subst (asm) produce_inner.simps)
          apply auto
          done
        done
      done
    subgoal for n t d lxs W
      apply (subst produce.code)
      apply (auto split: option.splits)
       subgoal
        apply (cases lxs)
         apply simp_all
        apply (subst produce_inner.simps)
        apply (auto split: if_splits event.splits sum.splits)
         subgoal for lxs' t'
           apply (drule meta_spec)
           apply (drule meta_spec)
           apply (drule meta_spec)
           apply (drule meta_spec[of _ "insert t' W"])
           apply (drule meta_mp)
            apply assumption
           apply (drule meta_mp)
           using Suc_ile_eq apply blast
           apply (subst (asm) produce.code)
           apply (auto split: option.splits)
           done
         subgoal for lxs' t'
              apply (drule meta_spec)
           apply (drule meta_spec)
           apply (drule meta_spec)
           apply (drule meta_spec[of _ "insert t' W"])
           apply (drule meta_mp)
            apply assumption
           apply (drule meta_mp)
           using Suc_ile_eq apply blast
           apply (subst (asm) produce.code)
           apply (auto split: option.splits)
           done
         done
       subgoal for op y ys lxs'
        apply (cases lxs)
          apply simp_all
         subgoal for x lxs''
        apply (subst (asm) produce_inner.simps)
           apply (auto simp add: Suc_ile_eq split: if_splits event.splits sum.splits; hypsubst_thin)
           apply (smt (verit, best) finite_produce_to_shift_produce in_lset_shift_eq insert_iff list.simps(15) produce_inner_to_finite_produce)
           apply (smt (verit, ccfv_threshold) finite_produce_to_shift_produce in_lset_shift_eq produce_inner_to_finite_produce set_ConsD)
           done
         done
       done
     done
   done

lemma produce_union_op_Inr_completeness:
  "Data (Inr t) d \<in> lset lxs \<Longrightarrow>
   Data t d \<in> lset (produce (union_op W) lxs)"
  apply (subst (asm) lset_conv_lnth)
  apply safe
  subgoal for n
    apply (induct n arbitrary: t d lxs W)
    subgoal for t d lxs
      apply (subst produce.code)
      apply (auto split: option.splits)
      subgoal
        apply (cases lxs)
         apply simp_all
        apply (subst produce_inner.simps)
        apply auto
        done
      subgoal for op y ys lys
        apply (cases lxs)
         apply simp_all
        subgoal for x lxs'
          apply hypsubst_thin
          apply (subst (asm) produce_inner.simps)
          apply auto
          done
        done
      done
    subgoal for n t d lxs W
      apply (subst produce.code)
      apply (auto split: option.splits)
       subgoal
        apply (cases lxs)
         apply simp_all
        apply (subst produce_inner.simps)
        apply (auto split: if_splits event.splits sum.splits)
         subgoal for lxs' t'
           apply (drule meta_spec)
           apply (drule meta_spec)
           apply (drule meta_spec)
           apply (drule meta_spec[of _ "insert t' W"])
           apply (drule meta_mp)
            apply assumption
           apply (drule meta_mp)
           using Suc_ile_eq apply blast
           apply (subst (asm) produce.code)
           apply (auto split: option.splits)
           done
         subgoal for lxs' t'
              apply (drule meta_spec)
           apply (drule meta_spec)
           apply (drule meta_spec)
           apply (drule meta_spec[of _ "insert t' W"])
           apply (drule meta_mp)
            apply assumption
           apply (drule meta_mp)
           using Suc_ile_eq apply blast
           apply (subst (asm) produce.code)
           apply (auto split: option.splits)
           done
         done
       subgoal for op y ys lxs'
        apply (cases lxs)
          apply simp_all
         subgoal for x lxs''
        apply (subst (asm) produce_inner.simps)
           apply (auto simp add: Suc_ile_eq split: if_splits event.splits sum.splits; hypsubst_thin)
           apply (smt (verit, best) finite_produce_to_shift_produce in_lset_shift_eq insert_iff list.simps(15) produce_inner_to_finite_produce)
           apply (smt (verit, ccfv_threshold) finite_produce_to_shift_produce in_lset_shift_eq produce_inner_to_finite_produce set_ConsD)
           done
         done
       done
     done
   done
  

end