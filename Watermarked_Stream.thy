theory Watermarked_Stream
  imports
    "Coinductive.Coinductive_List"
    "Linear_Temporal_Logic_on_Llists"
    "HOL-Library.BNF_Corec"
    "HOL-Library.Multiset"
    "Utils"
begin

datatype ('t, 'd) event = Data (tmp: 't) (data: 'd) | Watermark (wmk: "'t::order")

fun wms where
  "wms [] = {}"
| "wms (Watermark wm#xs) = insert wm (wms xs)"
| "wms (Data t d#xs) = wms xs"

lemma wms_empty[simp]:
  "\<forall> x \<in> set xs . is_Data x \<Longrightarrow> wms xs = {}"
  apply (induct xs)
   apply simp
  subgoal for x xs
    apply (cases x)
     apply (auto split: event.splits)
    done
  done

fun tmps where
  "tmps [] = {}"
| "tmps (Watermark wm#xs) = tmps xs"
| "tmps (Data t d#xs) =  insert t (tmps xs)"

lemma tmps_tmps:
  "wms xs = {} \<Longrightarrow> tmps xs = tmp ` set xs"
  apply (induct xs)
   apply simp
  apply auto
    apply (metis (no_types, opaque_lifting) event.sel(1) insertE insert_not_empty list.inject neq_Nil_conv tmps.simps(3) wms.elims)
   apply (metis event.sel(1) insert_iff insert_not_empty list.distinct(1) list.inject tmps.simps(3) wms.elims)
  apply (smt (verit, best) imageI insert_iff insert_not_empty list.inject neq_Nil_conv tmps.simps(3) wms.elims)
  done

coinductive monotone :: "('t::order, 'd) event llist \<Rightarrow> 't set \<Rightarrow> bool" where
  LNil: "monotone LNil WM"
| LConsR: "\<lbrakk> \<forall> wm' \<in> WM . \<not> wm' \<ge> wm; monotone xs (insert wm WM)\<rbrakk> \<Longrightarrow> monotone (LCons (Watermark wm) xs) WM"
| LConsL: "\<lbrakk> \<forall> wm \<in> WM . \<not> wm \<ge> t; monotone xs WM \<rbrakk> \<Longrightarrow> monotone (LCons (Data t d) xs) WM"

inductive monotone_prepend_cong for X where
  monotone_prepend_cong_base: "X xs S \<Longrightarrow> monotone_prepend_cong X xs S"
| monotone_prepend_cong_prepend: "monotone_prepend_cong X ys (wms xs \<union> S) \<Longrightarrow> monotone (llist_of xs) S \<Longrightarrow> monotone_prepend_cong X (xs @@- ys) S"

inductive_cases LNilE: "monotone LNil WM"
inductive_cases LConsWatermark: "monotone (LCons (Watermark wm) xs) WM"
inductive_cases LConsData: "monotone (LCons (Data t d) xs) WM"

lemma strict_monotone_coinduct_strict_monotone_prepend_cong1:
  assumes H1: "X lxs WM" 
    and H2:  "(\<And>x1 x2.
    X x1 x2 \<Longrightarrow>
    (\<exists>WM. x1 = LNil \<and> x2 = WM) \<or>
    (\<exists>WM wm xs. x1 = LCons (Watermark wm) xs \<and> x2 = WM \<and> (\<forall>wm'\<in>WM. \<not> wm \<le> wm') \<and> (monotone_prepend_cong X xs (insert wm WM) \<or> monotone xs (insert wm WM))) \<or>
    (\<exists>WM t xs d. x1 = LCons (Data t d) xs \<and> x2 = WM \<and> (\<forall>wm\<in>WM. \<not> t \<le> wm) \<and> (monotone_prepend_cong X xs WM \<or> monotone xs WM)))"  (is "\<And>x1 x2. X x1 x2 \<Longrightarrow> ?bisim x1 x2")
  shows "monotone lxs WM"
  using H1 apply -
proof (erule monotone.coinduct[OF monotone_prepend_cong_base])
  fix lxs WM
  assume "monotone_prepend_cong X lxs WM"
  then show "?bisim lxs WM"
    apply (induct lxs WM rule: monotone_prepend_cong.induct) 
    subgoal for xs S
      apply (drule assms)
      apply auto
      done
    subgoal for ys xs S
      apply (cases xs)
       apply simp
      subgoal for a list
        apply (cases a)
         apply (metis LConsData llist_of.simps(2) monotone_prepend_cong_prepend lshift.simps(2) wms.simps(3))
        apply (smt (verit, best) LConsWatermark Un_insert_left Un_insert_right llist_of.simps(2) monotone_prepend_cong_prepend lshift.simps(2) wms.simps(2))
        done
      done
    done
qed


abbreviation good_example where
  "good_example \<equiv> LCons (Data 3 STR ''data2'') (LCons (Watermark 3) (LCons (Data 4 STR ''data'') (LCons (Watermark (14::nat)) LNil)))"

lemma strict_monotone_good_example: "monotone good_example {}"
  apply (rule LConsL)
   apply simp
  apply (rule LConsR)
   apply simp
  apply (rule LConsL)
   apply simp
  apply (rule LConsR)
   apply simp
  apply (rule LNil)
  done

lemma Data_tail_ahead_of_t:
  "x  \<in> lset xs \<Longrightarrow> x = Data t d \<Longrightarrow> monotone (LCons (Watermark wm) xs) WM \<Longrightarrow> \<not> t \<le> wm"
  apply (induct xs arbitrary: wm t d WM rule: Coinductive_List.lset_induct)
   apply (meson LConsData LConsWatermark insertI1)
  subgoal for x' xs wm t d
    apply hypsubst_thin
    apply (erule monotone.cases)
      apply simp_all
    apply hypsubst_thin
    apply (cases x')
     apply (meson LConsData LConsR)
    apply (smt (verit) LConsR insert_commute insert_iff llist.distinct(1) llist.inject order_trans monotone.simps)
    done
  done

lemma Data_set_strict_monotone_not_GE:
  "Data t d \<in> lset xs \<Longrightarrow> monotone xs WM \<Longrightarrow> \<forall> wm \<in> WM . \<not> t \<le> wm"
  apply (induct xs arbitrary: WM rule: Coinductive_List.lset_induct)
   apply (meson LConsData)
  by (metis LConsData LConsWatermark event.exhaust insert_iff)

lemma strict_monotone_with_smaller_initial_watermark_Watermark:
  "monotone xs (insert wm WM) \<Longrightarrow> \<forall> wm' \<in> WM . \<not> wm' \<ge> wm \<Longrightarrow> 
   monotone (LCons (Watermark wm) xs) WM"
  apply (rule LConsR)
   apply simp_all
  done

lemma strict_monotone_remove_wm:
  "monotone xs (insert wm WM) \<Longrightarrow> monotone xs WM"
  apply (coinduction arbitrary: xs wm WM rule: monotone.coinduct)
  apply (erule monotone.cases)
    apply simp
   apply (metis in_mono insert_commute subset_insertI)
  apply auto
  done

lemma strict_monotone_drop_head: "monotone (LCons x xs) WM \<Longrightarrow> monotone xs WM"
  apply (cases x)
   apply (metis LConsData)
  subgoal for wm
    apply (cases xs)
    using monotone.LNil apply blast
    subgoal for x' xs'
      apply simp
      apply hypsubst_thin
      apply (frule LConsWatermark[where WM=WM and P="monotone (LCons x' xs') WM"])
      using strict_monotone_remove_wm apply blast
      apply simp
      done
    done
  done

lemma strict_monotone_ltl: "monotone xs initial_watermark \<Longrightarrow> monotone (ltl xs) initial_watermark"
  using strict_monotone_drop_head by (metis llist.exhaust ltl_simps(1) ltl_simps(2))

lemma strict_monotone_ldrop_aux:
  "monotone xs initial_watermark \<Longrightarrow> ldrop (enat n) xs = xs' \<Longrightarrow> monotone xs' initial_watermark"
  apply (induct n arbitrary: xs xs')
   apply (subst (asm) enat_0)
   apply (subst (asm) ldrop_0)
   apply simp
  subgoal for n' xs1 xs2
    by (metis eSuc_enat ldrop_ltl strict_monotone_ltl)
  done

lemma strict_monotone_ldrop:
  "monotone xs initial_watermark \<Longrightarrow> ldrop n xs = xs' \<Longrightarrow> monotone xs' initial_watermark"
  apply (cases n)
   apply (simp add: strict_monotone_ldrop_aux)
  by (simp add: monotone.LNil)

lemma strict_monotone_LCons_Watermark_insert:
  "monotone (LCons (Watermark wm) lxs) WM \<Longrightarrow> monotone lxs (insert wm WM)"
  apply (erule monotone.cases)
    apply simp_all
  done

lemma strict_monotone_coinduct_shift_strict_monotone_prepend_cong1:
  assumes
    "R lxs WM"
    and
    "(\<And>x1 x2.
    R x1 x2 \<Longrightarrow>
    (\<exists>WM. x1 = LNil \<and> x2 = WM) \<or>
    (\<exists>WM lxs xs. xs \<noteq> [] \<and> x1 = xs @@- lxs \<and> x2 = WM \<and> monotone (llist_of xs) WM \<and> (\<forall>wm'\<in>WM. \<forall> wm \<in> wms xs. \<not> wm \<le> wm') \<and> (\<forall>wm'\<in>WM. \<forall> t \<in> tmps xs. \<not> t \<le> wm') \<and> monotone_prepend_cong R lxs (wms xs \<union> WM))
   )" 
  shows "monotone lxs WM"
  using assms apply -
  apply (drule strict_monotone_coinduct_strict_monotone_prepend_cong1)
   defer
   apply simp
  subgoal for lxs WM
    apply (drule meta_spec[of _ lxs])
    apply (drule meta_spec[of _ WM])
    apply (drule meta_mp)
     apply assumption
    apply (elim exE disjE conjE)
     apply simp
    subgoal for WMa lxsa xs
      apply (cases xs)
       apply simp
      apply hypsubst_thin
      subgoal for x xs
        apply (cases x)
        subgoal
          apply hypsubst_thin
          apply (rule disjI2)+
          apply simp
          apply (rule disjI1)
          apply (rule monotone_prepend_cong_prepend)
           apply assumption
          using strict_monotone_drop_head apply blast
          done
        subgoal
          apply hypsubst_thin
          apply (rule disjI2)
          apply (rule disjI1)
          apply simp
          apply (rule disjI1)
          apply (rule monotone_prepend_cong_prepend)
           apply force   
          apply (meson LConsWatermark)
          done
        done
      done
    done
  done


lemma Watermark_stops_at_aux:
  "x \<in> lset lxs \<Longrightarrow>
   x = Watermark wm \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   enat n < llength lxs \<Longrightarrow>
   lnth lxs n = Watermark wm \<Longrightarrow>
   Watermark wm \<notin> lset (ldrop (enat (Suc n)) lxs)"
  apply (induct lxs arbitrary: n wm rule: lset_induct)
  subgoal for xs
    apply simp
    apply (erule monotone.cases)
      apply simp_all
    apply hypsubst_thin
    apply (metis LConsWatermark dual_order.order_iff_strict in_lset_finds_tail insert_iff ldrop_enat ldropn_Suc_LCons strict_monotone_ldrop_aux)
    done
  subgoal for x xs
    apply (erule monotone.cases)
      apply simp_all
     apply (metis Suc_ile_eq bot_nat_0.not_eq_extremum event.inject(2) gr0_conv_Suc ldrop_0 ldrop_enat ldropn_Suc_LCons ldropn_eq_LConsD lhd_LCons lhd_ldrop lnth_Suc_LCons strict_monotone_remove_wm zero_enat_def)
    apply (metis One_nat_def Suc_ile_eq Suc_pred eSuc_enat event.distinct(1) ldrop_eSuc_LCons less_SucE lnth_LCons' zero_less_Suc)
    done
  done

lemma Data_stops_at_aux:
  "x \<in> lset lxs \<Longrightarrow>
   x = Watermark wm \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   enat n < llength lxs \<Longrightarrow>
   lnth lxs n = Watermark wm \<Longrightarrow>
   \<forall> d . Data wm d \<notin> lset (ldrop (enat (Suc n)) lxs)"
  apply (induct lxs arbitrary: n wm rule: lset_induct)
  subgoal for xs
    apply simp
    apply (erule monotone.cases)
      apply simp_all
    apply hypsubst_thin
    apply (metis Data_tail_ahead_of_t LConsR dual_order.order_iff_strict event.distinct(1) in_lset_ldropD insert_iff llist.simps(19))
    done
  subgoal
    apply (erule monotone.cases)
      apply simp_all
     apply (metis One_nat_def Suc_ile_eq Suc_pred eSuc_enat event.inject(2) ldrop_eSuc_LCons less_SucE lnth_LCons' strict_monotone_remove_wm zero_less_Suc)
    apply (metis One_nat_def Suc_ile_eq Suc_pred eSuc_enat event.distinct(1) ldrop_eSuc_LCons less_SucE lnth_LCons' zero_less_Suc)
    done
  done

lemma Data_stops_at:
  "monotone lxs WM \<Longrightarrow>
   enat n < llength lxs \<Longrightarrow>
   lnth lxs n = Watermark wm \<Longrightarrow>
   \<forall> d . Data wm d \<notin> lset (ldrop (enat (Suc n)) lxs)"
  by (metis Data_stops_at_aux in_lset_conv_lnth)

lemma Watermark_stops_at:
  "monotone lxs WM \<Longrightarrow>
   enat n < llength lxs \<Longrightarrow>
   lnth lxs n = Watermark wm \<Longrightarrow>
   Watermark wm \<notin> lset (ldrop (enat (Suc n)) lxs)"
  by (meson Watermark_stops_at_aux in_lset_ldropD)

lemma strict_monotone_lfinite_lfilter_le_t_alt:
  "monotone lxs WM \<Longrightarrow>
   Watermark wm \<in> lset lxs \<Longrightarrow>
   wm \<ge> t \<Longrightarrow>
   lfinite (lfilter (\<lambda> x . case x of Data t' d \<Rightarrow> t' \<le> t | Watermark wm \<Rightarrow> False) lxs)"
  apply (cases "lfinite lxs")
  using lfinite_lfilterI apply blast
  subgoal
    apply (subst (asm) (1) in_lset_conv_lnth)
    apply (elim bexE exE conjE)
    subgoal for n
      apply (rule ldropn_lfinite_lfinter[where n=n])
       apply simp
      apply safe
      subgoal for x
        apply (induct n arbitrary: lxs WM)
        subgoal for lxs WM
          apply (cases lxs)
           apply simp_all
          apply (smt (verit) Data_tail_ahead_of_t event.case_eq_if event.exhaust_sel event.simps(6) order_trans)
          done
        subgoal for n lxs WM
          apply (cases lxs)
           apply simp_all
          using Suc_ile_eq strict_monotone_drop_head apply blast
          done
        done
      done
    done
  done

lemma strict_monotone_lfinite_lfilter_eq_t_alt:
  "monotone lxs WM \<Longrightarrow>
   Watermark wm \<in> lset lxs \<Longrightarrow>
   wm \<ge> t \<Longrightarrow>
   lfinite (lfilter (\<lambda> x . case x of Data t' d \<Rightarrow> t' = t | Watermark wm \<Rightarrow> False) lxs)"
  apply (cases "lfinite lxs")
  using lfinite_lfilterI apply blast
  subgoal
    apply (subst (asm) (1) in_lset_conv_lnth)
    apply (elim bexE exE conjE)
    subgoal for n
      apply (rule ldropn_lfinite_lfinter[where n=n])
       apply simp
      apply safe
      subgoal for x
        apply (induct n arbitrary: lxs WM)
        subgoal for lxs WM
          apply (cases lxs)
           apply simp_all
          apply (smt (verit, ccfv_threshold) Data_tail_ahead_of_t event.case_eq_if event.exhaust_sel event.simps(6))
          done
        subgoal for n lxs WM
          apply (cases lxs)
           apply simp_all
          using Suc_ile_eq strict_monotone_drop_head apply blast
          done
        done
      done
    done
  done

lemma Data_stops_at_b:
  "stop_gathering_location t lxs = n \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   lnth lxs n = Watermark wm \<Longrightarrow>
   \<not> lfinite lxs \<Longrightarrow>
   \<forall> d . Data wm d \<notin> lset (ldrop (enat (Suc n)) lxs)"
  apply (rule Data_stops_at)
    apply assumption
   apply (simp add: not_lfinite_llength)
  apply assumption
  done

lemma tail_incomparable:
  "Watermark wm \<in> lset lxs \<Longrightarrow>
   monotone (LCons (Watermark wm') lxs) WM \<Longrightarrow>
   wm \<le> wm' \<Longrightarrow>
   False"
  by (metis LConsWatermark in_lset_finds_tail insertI1 strict_monotone_ldrop_aux)

lemma strict_monotone_LCons_Watermark_Data_not_ge:
  "monotone (LCons (Watermark wm) lxs) WM \<Longrightarrow>
   Data t batch \<in> lset lxs \<Longrightarrow> 
   \<not> t \<le> wm"
  apply (erule monotone.cases)
    apply (auto simp add: Data_set_strict_monotone_not_GE)
  done

lemma Watermark_in_lxs_in_sub:
  "t \<le> wm \<Longrightarrow>
   Watermark wm \<in> lset lxs \<Longrightarrow>
   lnth lxs n = Data t d  \<Longrightarrow>
   enat n < llength lxs \<Longrightarrow> 
   monotone lxs WM \<Longrightarrow>
   lfinite lxs \<Longrightarrow>
  \<forall>k\<in>{Suc n..<the_enat (llength lxs)}. \<forall>wm'\<ge>t. lnth lxs k \<noteq> Watermark wm' \<Longrightarrow>
  False"
  apply (induct "llength lxs")
  subgoal for n'
    apply (induct n' arbitrary: lxs n WM)
    using zero_enat_def apply force
    subgoal for n' lxs n WM
      apply (cases lxs)
       apply simp
      subgoal for x lxs'
        apply (drule meta_spec[of _ "lxs'"])
        apply simp
        apply (cases "Watermark wm = x")
         apply (metis event.simps(4) iless_Suc_eq in_lset_conv_lnth insertE llength_LCons lset_LCons strict_monotone_LCons_Watermark_Data_not_ge)
        apply (drule meta_spec[of _ "n - 1"])
        apply (drule meta_spec[of _ WM])
        apply (drule meta_mp)
         apply (metis co.enat.sel(2) eSuc_enat)
        apply (drule meta_mp)
         apply meson
        apply (drule meta_mp)
         apply (metis atLeastLessThan_iff co.enat.sel(2) eSuc_enat enat_ord_simps(2) image_Suc_atLeastLessThan image_eqI in_lset_conv_lnth lnth_LCons' lnth_Suc_LCons the_enat.simps zero_le)
        apply (drule meta_mp)
         apply (metis (no_types, lifting) Suc_ile_eq diff_is_0_eq in_lset_conv_lnth le_add_diff_inverse linorder_not_le order.strict_iff_order plus_1_eq_Suc zero_enat_def zero_le)
        apply (drule meta_mp)
        using strict_monotone_drop_head apply blast
        apply (drule meta_mp)
        subgoal
          apply auto
          apply (cases n)
           apply (metis atLeastLessThan_iff eSuc_enat eSuc_inject linorder_not_le lnth_Suc_LCons not_less_eq_eq the_enat.simps zero_less_Suc)
          apply auto
          apply (metis atLeastLessThan_iff eSuc_enat eSuc_inject less_Suc_eq_le linorder_not_le lnth_Suc_LCons the_enat.simps)
          done
        apply simp
        done
      done
    done
  apply (metis llength_eq_infty_conv_lfinite)
  done

definition stop_gathering_location :: "'t \<Rightarrow> ('t::order, 'b) event llist \<Rightarrow> nat" where
  "stop_gathering_location t xs = (if lfinite xs 
                                   then the_enat (llength xs)
                                   else LEAST x . (case lnth xs x of
                                                     Data _ _ \<Rightarrow> False 
                                                   | Watermark wm \<Rightarrow> t \<le> wm))"

lemma stop_gathering_location_finds_wm:
  "\<exists> wm \<ge> t. Watermark wm \<in> lset lxs \<Longrightarrow>
   \<not> lfinite lxs \<Longrightarrow>
   \<exists> n wm . stop_gathering_location t lxs = n \<and> lnth lxs n = Watermark wm \<and> wm \<ge> t"
  apply simp
  unfolding stop_gathering_location_def
  apply simp
  by (smt (verit) LeastI event.case_eq_if event.collapse(2) event.simps(6) lset_conv_lnth mem_Collect_eq)

lemma strict_monotone_lfinite_lfilter_le_t:
  "monotone lxs WM \<Longrightarrow>
   \<exists> wm \<ge> t. Watermark wm \<in> lset lxs \<Longrightarrow>
   lfinite (lfilter (\<lambda> x . case x of Data t' d \<Rightarrow> t' \<le> t | Watermark wm \<Rightarrow> False) lxs)"
  apply (cases "lfinite lxs")
  using lfinite_lfilterI apply blast
  subgoal
    apply (rule ldropn_lfinite_lfinter[where n="Suc (stop_gathering_location t lxs)"])
     apply (simp add: not_lfinite_llength)
    unfolding stop_gathering_location_def
    apply simp
    apply safe
    subgoal for x
      apply (cases x)
      subgoal for t' d'
        apply (subgoal_tac "\<exists>n wm. stop_gathering_location t lxs = n \<and> lnth lxs n = Watermark wm \<and> wm \<ge> t")
         defer
        using stop_gathering_location_finds_wm apply blast
        apply (elim conjE exE)
        apply (frule Data_stops_at_b)
           apply assumption+
        apply hypsubst_thin
        apply simp
        apply (metis Data_tail_ahead_of_t enat_ord_code(4) ldrop_enat ldropn_Suc_conv_ldropn not_lfinite_llength order_trans stop_gathering_location_def strict_monotone_ldrop)
        done                 
      subgoal for wm'
        by simp
      done
    done
  done

definition productive where
  "productive s \<equiv> (\<forall> t . alwll ((holdsll (\<lambda> x . (\<exists> d . x = Data t d))) impll (evll (wholdsll (\<lambda> x . (\<exists> u \<ge> t . x = Watermark u))))) s) \<and>
                   alwll (evll (wholdsll is_Data)) s"

inductive productive_prepend_cong1 for X where
  productive_prepend_cong1_base: "X xs \<Longrightarrow> productive_prepend_cong1 X xs"
| productive_prepend_cong1_prepend_1: "productive_prepend_cong1 X ys \<Longrightarrow>
  \<forall> n < length xs . \<forall> t d . xs ! n = Data t d \<longrightarrow> (\<exists> wm .wm \<ge> t \<and> Watermark wm \<in> lset (drop (Suc n) xs @@- ys)) 
    \<Longrightarrow> productive_prepend_cong1 X (xs @@- ys)"


coinductive productive' where
  "lfinite xs \<Longrightarrow> productive' xs"
| "\<not> lfinite xs \<Longrightarrow> (\<exists>u \<in> Watermark -` lset xs. u \<ge> t) \<Longrightarrow> productive' xs \<Longrightarrow> productive' (LCons (Data t d) xs)"
| "\<not> lfinite xs \<Longrightarrow> \<exists> t' d' .Data t' d' \<in> lset xs \<Longrightarrow>  productive' xs \<Longrightarrow> productive' (LCons (Watermark t) xs)"

lemma productive_productive': "productive ws \<Longrightarrow> productive' ws"
  apply (coinduction arbitrary: ws)
  subgoal for ws
    apply (cases ws)
     apply simp
    subgoal for x xs
      apply (cases x)
      subgoal for t d
        apply simp
        apply hypsubst_thin
        apply (simp only: productive_def alwll_LCons_iff  holdsll_LCons wholdsll_LCons
            productive_def[symmetric] sum.simps prod.simps simp_thms)
        apply (erule conjE)
        apply (drule spec[of _ t])
        apply (erule thin_rl)
        apply (drule conjunct2)
        using evll_wholdsll_lfinite apply fastforce
        done
      subgoal for wm
        apply simp
        apply (simp only: productive_def alwll_LCons_iff holdsll_LCons wholdsll_LCons
            productive_def[symmetric] sum.simps prod.simps simp_thms)
        apply (metis alwllD evll_wholdsll_lfinite is_Data_def lfinite_code(1))
        done
      done
    done
  done


lemma productive'_productive: "productive' ws \<Longrightarrow> productive ws"
  unfolding productive_def
  apply (intro allI conjI)
  subgoal for t
    apply (coinduction arbitrary: ws)
    subgoal for ws
      apply (cases ws)
       apply simp
      subgoal for x xs
        apply (cases x)
        subgoal for u d
          apply (hypsubst_thin)
          apply (erule productive'.cases)
            apply (auto simp: lfinite_evll_wholdsll lset_induct)
          subgoal
            apply (induct xs rule: lfinite_induct)
             apply (auto simp: lnull_def) []
            subgoal for xs
              apply (cases xs)
               apply (auto simp: alwll_LCons_iff lfinite_evll_wholdsll productive'.intros)
              done
            done
          subgoal for wm
            apply (hypsubst_thin)
            apply (erule productive'.cases)
              apply (auto simp: base evll.step lfinite_evll_wholdsll lset_induct)
            done
          done
        subgoal for wm
          apply (hypsubst_thin)
          apply (erule productive'.cases)
            apply (auto simp: base evll.step lfinite_evll_wholdsll lset_induct)
          using productive'.intros(1) apply blast
          done
        done
      done
    done
  apply (coinduction arbitrary: ws S) 
  subgoal for ws
    apply (cases ws)
     apply simp
    subgoal for x xs
      apply (cases x)
      subgoal for u d
        apply (hypsubst_thin)
        apply (erule productive'.cases)
          apply (auto simp:  alwll_evll_wholdsll_alt)
        done
      subgoal for u
        apply hypsubst_thin
        apply (erule productive'.cases)
          apply (auto simp:  lfinite_evll_wholdsll alwll_evll_wholdsll_alt lset_induct)
        apply (metis event.disc(1) evll.step in_lset_conv_lnth lnth_imp_evll_wholdsll)
        done
      done
    done
  done

lemma productive_alt: "productive = productive'"
  unfolding fun_eq_iff using productive_productive' productive'_productive by blast

lemmas productive_intros = productive'.intros[folded productive_alt]
lemmas productive_cases = productive'.cases[folded productive_alt]
lemmas productive_coinduct[coinduct pred] = productive'.coinduct[folded productive_alt]

lemma productive_drop_head: "productive (LCons a xs) \<Longrightarrow> productive xs"
  unfolding productive_def
  apply safe
  subgoal for t
    apply (coinduction rule: alwll.coinduct)
    apply (metis (mono_tags) alwll.simps alwll_LConsD)
    done
  apply (coinduction rule: alwll.coinduct)
  by (metis (mono_tags, lifting) alwll.cases alwll_LConsD)

lemma productive_lappendD[rotated]: "lfinite xs \<Longrightarrow> productive (lappend xs ys) \<Longrightarrow> productive ys"
  by (induct xs rule: lfinite_induct)
    (auto simp add: lnull_def neq_LNil_conv dest!: productive_drop_head)

lemma productive'_coinduct_prepend_cong1:
  assumes H1: "X lxs" 
    and H2:  "(\<And>x1.
    X x1 \<Longrightarrow>
    (\<exists>xs. x1 = xs \<and> lfinite xs) \<or>
    (\<exists>xs t d. x1 = LCons (Data t d) xs \<and> \<not> lfinite xs \<and> Bex (Watermark -` lset xs) ((\<le>) t) \<and> (productive_prepend_cong1 X xs \<or> productive' xs)) \<or>
    (\<exists>xs wm. x1 = LCons (Watermark wm) xs \<and> \<not> lfinite xs \<and> (\<exists>t' d'. Data t' d' \<in> lset xs) \<and> (productive_prepend_cong1 X xs \<or> productive' xs)))" (is "\<And>x1 . X x1 \<Longrightarrow> ?bisim x1")
  shows "productive' lxs"
  using H1 apply -
proof (erule productive'.coinduct[OF productive_prepend_cong1_base])
  fix lxs
  assume  "productive_prepend_cong1 X lxs"
  then show "?bisim lxs"
    apply (induct lxs rule: productive_prepend_cong1.induct) 
    subgoal for xs
      apply (drule assms)
      apply auto
      done
    subgoal for ys xs
      apply (cases xs)
       apply simp
      subgoal for a list
        apply (cases a)
         apply hypsubst_thin
        subgoal for t' d'
          apply (elim exE disjE conjE)
              apply (rule disjI1)
              apply (metis lappend_llist_of lfinite_lappend lfinite_llist_of)
             apply (rule disjI2)
             apply (fastforce simp add: productive_prepend_cong1_prepend_1)+
          done
        apply hypsubst_thin
        subgoal for wm
          apply (elim exE disjE conjE)
              apply (rule disjI1)
              apply auto[1]
             apply (rule disjI2)+
             apply (fastforce simp add: productive_prepend_cong1_prepend_1)+
          done
        done
      done
    done
qed

lemma productive'_coinduct_prepend_cong1_shift:
  assumes H1: "X lxs" 
    and H2:  "(\<And>x1.
    X x1 \<Longrightarrow>
    (\<exists>lxs. x1 = lxs \<and> lfinite lxs) \<or>
    (\<exists>lxs t d wm. x1 = [Data t d, Watermark wm] @@- lxs \<and> t \<le> wm \<and> \<not> lfinite lxs \<and> productive_prepend_cong1 X lxs))" (is "\<And>x1 . X x1 \<Longrightarrow> ?bisim x1")
  shows "productive' lxs"
  using assms apply -
  apply (erule productive'_coinduct_prepend_cong1)
  subgoal for lxs
    apply (drule meta_spec)
    apply (drule meta_mp)
     apply assumption
    apply (elim exE conjE disjE)
     apply simp
    apply hypsubst_thin
    apply (rule disjI2)
    apply (rule disjI1)
    apply simp
    apply (rule conjI)
     apply blast
    apply (rule disjI1)
    subgoal for lxs t d wm
      using productive_prepend_cong1_prepend_1[where xs="[Watermark wm]"] apply simp
      apply assumption
      done
    done
  done

lemma productive'_coinduct_prepend_cong1_shift_gen:
  assumes H1: "X lxs" 
    and H2:  "(\<And>x1.
    X x1 \<Longrightarrow>
    (\<exists>lxs. x1 = lxs \<and> lfinite lxs) \<or>
    (\<exists>lxs ys wm. x1 = ys @@- lxs \<and> \<not> List.null ys \<and> (\<exists> t d . Data t d \<in> lset x1) \<and>
    (\<forall> n < length ys . (\<forall> t d . ys ! n = Data t d \<longrightarrow> (\<exists> wm .Watermark wm \<in> lset (drop (Suc n) ys @@- lxs) \<and> t \<le> wm ))) \<and>
     \<not> lfinite lxs \<and> productive_prepend_cong1 X lxs))" (is "\<And>x1 . X x1 \<Longrightarrow> ?bisim x1")
  shows "productive' lxs"
  using assms apply -
  apply (erule productive'_coinduct_prepend_cong1)
  subgoal for lxs
    apply (drule meta_spec)
    apply (drule meta_mp)
     apply assumption
    apply (elim exE conjE disjE)
     apply simp
    subgoal for lxs' ys wm
      apply hypsubst_thin
      apply (rule disjI2)
      apply (cases ys)
      using null_rec(2) apply blast
      subgoal for y ys'
        apply (cases y)
        subgoal
          apply auto
               apply fastforce
              apply (rule productive_prepend_cong1_prepend_1)
               apply assumption
              apply force
             apply fastforce
            apply (rule productive_prepend_cong1_prepend_1)
             apply assumption
            apply force
           apply fastforce
          apply (rule productive_prepend_cong1_prepend_1)
           apply assumption
          apply force
          done
        apply auto
         apply (rule productive_prepend_cong1_prepend_1)
          apply assumption
         apply force
        apply (rule productive_prepend_cong1_prepend_1)
         apply assumption
        apply force
        done
      done
    done
  done

lemma productive_coinduct_prepend_cong1_shift:
  assumes H1: "X lxs" 
    and H2:  "(\<And>x1.
    X x1 \<Longrightarrow>
    (\<exists>xs. x1 = xs \<and> lfinite xs) \<or>
    (\<exists>xs t d wm. x1 = [Data t d, Watermark wm] @@- xs \<and> t \<le> wm \<and> \<not> lfinite xs \<and> productive_prepend_cong1 X xs))" (is "\<And>x1 . X x1 \<Longrightarrow> ?bisim x1")
  shows "productive lxs"
  using assms apply (simp add: productive_alt)
  apply (rule productive'_coinduct_prepend_cong1_shift)
   apply assumption
  using H2 by presburger

lemma productive_coinduct_prepend_cong1_shift_gen:
  assumes H1: "X lxs" 
    and H2:  "(\<And>x1.
    X x1 \<Longrightarrow>
    (\<exists>lxs. x1 = lxs \<and> lfinite lxs) \<or>
    (\<exists>lxs xs. x1 = xs @@- lxs \<and> \<not> List.null xs \<and> (\<exists> t d . Data t d \<in> lset x1) \<and> (\<forall> n < length xs . (\<forall> t d . xs ! n = Data t d \<longrightarrow> (\<exists> wm .Watermark wm \<in> lset (drop (Suc n) xs @@- lxs) \<and> t \<le> wm ))) \<and>
     \<not> lfinite lxs \<and> productive_prepend_cong1 X lxs))" (is "\<And>x1 . X x1 \<Longrightarrow> ?bisim x1")
  shows "productive lxs"
  using assms apply (simp add: productive_alt)
  apply (rule productive'_coinduct_prepend_cong1_shift_gen)
   apply assumption
  using H2 by presburger

lemma productivity_good_example: "productive good_example"
  unfolding productive_def
  apply safe
  subgoal for t
    apply (rule alwll)
     apply simp
     apply safe
     apply (rule evll.step)
     apply (rule evll.base)
     apply simp_all
    apply (rule alwll)
     apply simp_all
    apply (rule alwll)
     apply simp_all
     apply safe
     apply (rule evll.step)
     apply (rule evll.base)
     apply simp_all
    apply (rule alwll)
     apply simp_all
    done
  apply (rule alwll)
   apply (rule evll.step)
   apply (rule evll.step)
   apply (rule evll.base)
   apply simp
  apply simp
  apply (rule alwll)
   apply (rule evll.step)
   apply (rule evll.base)
   apply simp
  apply simp
  apply (rule alwll)
   apply (rule evll.base)
   apply simp
  apply simp
  apply (rule alwll)
   apply (rule evll.step)
   apply (rule evll.base)
   apply simp
  apply simp
  done

lemma productive_ldrop: "productive xs \<Longrightarrow> productive (ldrop (enat n) xs)"
  apply (induct n)
   apply simp_all
  using zero_enat_def apply fastforce
  apply (metis ldrop_eSuc_ltl ldrop_enat ltl_ldropn ltl_simps(1) ltl_simps(2) neq_LNil_conv productive_drop_head)
  done

lemma productive_finds_data:
  "productive lxs \<Longrightarrow>
   lnth lxs n = Data t d \<Longrightarrow>
   \<not> lfinite lxs \<Longrightarrow>
   \<exists> m > n . \<exists> wm \<ge> t . lnth lxs m = Watermark wm"
  apply (subgoal_tac "evll (wholdsll (\<lambda>x. \<exists>u\<ge>t. x = Watermark u)) (ldrop (enat n) lxs)")
   apply (drule evll_wholdsll_finds_n_alt)
    apply simp
   apply safe
  subgoal for n' u
    apply (rule exI[of _ "n' + n"])
    apply simp
    apply safe
     apply (metis enat_ord_code(4) event.simps(4) ldrop_enat ldropn_Suc_conv_ldropn llength_eq_infty_conv_lfinite lnth_0 zero_less_iff_neq_zero)
    by (simp add: not_lfinite_llength)
  apply (drule productive_ldrop[where n=n])
  unfolding productive_def
  apply safe  
  apply (drule spec[where x=t])
  apply (simp add: ldrop_enat)
  apply (subst ldropn_Suc_conv_ldropn[symmetric])
   apply (simp add: not_lfinite_llength)
  apply (subst (asm) (2) ldropn_Suc_conv_ldropn[symmetric])
   apply (simp add: not_lfinite_llength)
  apply auto
  done


lemma strict_monotone_productive_lfinite_lfilter_eq_t:
  "monotone lxs WM \<Longrightarrow>
   productive lxs \<Longrightarrow>
   lfinite (lfilter (\<lambda> x . case x of Data t' d \<Rightarrow> t' = t | Watermark wm \<Rightarrow> False) lxs)"
  apply (cases "lfinite lxs")
  using lfinite_lfilterI apply blast
  apply (cases "\<exists> d . Data t d \<in> lset lxs")
  subgoal
    apply (subst (asm) in_lset_conv_lnth)
    apply (elim conjE exE)
    subgoal for d n
      apply (frule productive_finds_data[where t=t and d=d and n= n])
        apply assumption+
      apply (elim conjE exE bexE)
      subgoal for m wm
        apply (frule Data_stops_at[where n=m and wm=wm])
          apply (simp add: not_lfinite_llength)
         apply simp
        apply (frule Watermark_stops_at[where n=m and wm=wm])
          apply (simp add: not_lfinite_llength)
         apply simp
        apply (rule ldropn_lfinite_lfinter[where n="Suc m"])
         apply (simp add: not_lfinite_llength)
        apply safe
        subgoal for x
          apply (cases x)
           apply simp
           apply (metis Data_tail_ahead_of_t enat_ord_code(4) ldrop_enat ldropn_Suc_conv_ldropn not_lfinite_llength strict_monotone_ldrop)
          apply simp
          done
        done
      done
    done
  subgoal
    apply (cases "\<exists> d . Watermark t \<in> lset lxs")
    subgoal
      apply (subst (asm) (2) in_lset_conv_lnth)
      apply (elim bexE exE conjE)
      subgoal for d m
        apply (frule Watermark_stops_at[where n=m and wm=t])
          apply (simp add: not_lfinite_llength)
         apply assumption
        apply (rule ldropn_lfinite_lfinter[where n="Suc m"])
         apply (simp add: not_lfinite_llength)
        apply safe
        subgoal for x
          apply (cases x)
           apply simp
           apply (meson in_lset_ldropnD)
          apply (simp add: ldrop_enat)
          done
        done
      done
    apply (rule ldropn_lfinite_lfinter[where n="0"])
     apply (simp add: not_lfinite_llength)
    apply simp
    apply (smt (verit, best) event.split_sel_asm inf_bool_def)
    done
  done

term case_event

abbreviation "data_list_at lxs t \<equiv> List.map_filter (case_event (\<lambda>t d. Some d) Map.empty) (list_of (lfilter (\<lambda> x . case x of Data t' d \<Rightarrow> t' = t | Watermark wm \<Rightarrow> False) lxs))"
definition "coll lxs t = mset (data_list_at lxs t)"

definition "ts lxs t = {t' . \<exists> d' . Data t' d' \<in> lset lxs \<and> t' \<le> t}"

lemma set_inv_llist_of_eq_lset:
  "lfinite lxs \<Longrightarrow>
   set (inv llist_of lxs) = lset lxs"
  apply (induct lxs rule: lfinite_rev_induct)
   apply (simp add: inv_f_eq)
  apply simp
  apply (smt (verit, best) Un_insert_right f_inv_into_f lappend_LNil2 lfinite_LConsI lfinite_eq_range_llist_of lfinite_lappend lset_LCons lset_lappend_conv lset_llist_of)
  done

lemma ts_LCons_Watermark[simp]:
  "ts (LCons (Watermark wm) lxs) t = ts lxs t"
  unfolding ts_def
  apply simp
  done

lemma ts_strict_monotone_eq_empty:   
  "monotone (LCons (Watermark wm) lxs) WM \<Longrightarrow>
   ts (LCons (Watermark wm) lxs) wm = {}"
  unfolding ts_def
  apply simp
  apply (meson Data_tail_ahead_of_t)
  done

lemma ts_strict_monotone_eq_empty_ltl:   
  "monotone (LCons (Watermark wm) lxs) WM \<Longrightarrow>
   ts lxs wm = {}"
  unfolding ts_def
  apply simp
  apply (meson Data_tail_ahead_of_t)
  done

term ts

definition "ts' lxs t = tmp ` set (list_of (lfilter (\<lambda> x . case x of Data t' d \<Rightarrow> t' \<le> t | Watermark wm \<Rightarrow> False) lxs))"

lemma ts_eq_ts':
  "monotone lxs WM \<Longrightarrow>
   \<exists> wm\<ge>t. Watermark wm \<in> lset lxs \<Longrightarrow>
   ts lxs t = ts' lxs t"
  unfolding ts_def ts'_def list_of_def
  apply (subgoal_tac "lfinite (lfilter (case_event (\<lambda> t' d. t' \<le> t) (\<lambda>wm. False)) lxs)")
   defer
  using strict_monotone_lfinite_lfilter_le_t apply blast
  apply (simp only: if_True)
  apply (subst set_inv_llist_of_eq_lset)
  using strict_monotone_lfinite_lfilter_le_t apply blast
  apply auto
    apply (metis (no_types, lifting) event.sel(1) event.simps(5) imageI mem_Collect_eq)
   apply (metis event.case_eq_if event.collapse(1))
  apply (metis event.case_eq_if)
  done

lemma finite_ts[simp]:
  "monotone lxs WM \<Longrightarrow>
   \<exists> wm\<ge>t . Watermark wm \<in> lset lxs \<Longrightarrow>
   finite (ts lxs t)"
  apply (subst ts_eq_ts')
    apply assumption+
  unfolding ts'_def
  apply blast
  done

lemma ts_Data_in[simp]:
  "ts (LCons (Data t' d) lxs) t = (if t' \<le> t then insert t' (ts lxs t) else ts lxs t)"
  unfolding ts_def
  apply (cases "t' \<le> t")
   apply (simp only: if_True lset_LCons)
   apply blast
  apply auto
  done

definition "ws lxs t = {wm . \<exists> n m. enat n < llength lxs \<and> lnth lxs n = Watermark wm \<and> \<not> wm \<ge> t \<and> enat m < llength lxs \<and> lnth lxs m = Watermark t \<and> n < m}"

lemma ws_LCons_Data[simp]:
  "ws (LCons (Data t d) lxs) wm = ws lxs wm"
  unfolding ws_def
  apply auto
  subgoal for x n m
    apply (rule exI[of _ "n - 1"])
    apply auto
      apply (metis Suc_ile_eq Suc_pred bot_nat_0.not_eq_extremum event.distinct(1) lnth_LCons')
     apply (simp add: lnth_LCons')
     apply (metis One_nat_def event.simps(4))
    apply (metis One_nat_def Suc_ile_eq Suc_less_eq Suc_pred bot_nat_0.not_eq_extremum event.distinct(1) lnth_LCons')
    done
  subgoal for x n m
    apply (rule exI[of _ "Suc n"])
    apply auto
    using Suc_ile_eq apply blast
    by (metis Suc_ile_eq Suc_less_eq lnth_Suc_LCons)
  done

lemma wm_not_in_ws[simp]:
  "\<not> wm\<in> ws lxs wm"
  apply (simp add: ws_def)
  done

lemma ws_correct:
  "t \<in> ws lxs wm \<Longrightarrow>
   \<not> t \<ge> wm"
  apply (simp add: ws_def)
  by blast

lemma ts_Watermark_in:
  "ws (LCons (Watermark wm') lxs) wm = (if wm' \<ge> wm then ws lxs wm else (if Watermark wm \<in> lset lxs then insert wm' (ws lxs wm) else ws lxs wm))"
  unfolding ws_def
  apply auto
        apply (smt (verit, del_insts) One_nat_def Suc_ile_eq Suc_pred bot_nat_0.not_eq_extremum enat_ord_simps(2) event.inject(2) linorder_not_less lnth_LCons' order_less_imp_le)
       apply (metis Suc_ile_eq Suc_less_eq lnth_Suc_LCons)
      apply (smt (verit, del_insts) One_nat_def Suc_ile_eq Suc_pred bot_nat_0.not_eq_extremum enat_ord_simps(2) event.inject(2) linorder_not_less lnth_LCons' order_less_imp_le)
     apply (metis eSuc_enat ileI1 in_lset_conv_lnth lnth_0 lnth_Suc_LCons zero_enat_def zero_le zero_less_Suc)
    apply (metis Suc_less_eq eSuc_enat ileI1 lnth_Suc_LCons)
   apply (metis Suc_ile_eq Suc_le_D Suc_le_eq in_lset_conv_lnth lnth_Suc_LCons)
  apply (simp add: in_lset_conv_lnth)
  done

lemma ws_strict_monotone_empty:
  "monotone (LCons (Watermark wm) lxs) WM \<Longrightarrow>
   ws lxs wm = {}"
  apply (erule monotone.cases)
    apply simp_all
  unfolding ws_def
  apply auto
  apply (metis in_lset_conv_lnth order_class.order_eq_iff strict_monotone_with_smaller_initial_watermark_Watermark tail_incomparable)
  done

lemma ws_strict_monotone_LCons_empty:
  "monotone (LCons (Watermark wm) lxs) WM \<Longrightarrow>
   ws (LCons (Watermark wm) lxs) wm = {}"
  apply (erule monotone.cases)
    apply simp_all
  unfolding ws_def
  apply (auto simp add: ts_Watermark_in)
  apply (metis LConsR Suc_ile_eq diff_Suc_1 dual_order.refl in_lset_conv_lnth less_imp_Suc_add lnth_LCons' not_less_zero tail_incomparable)
  done

definition "sync_ts lxs t = {t' \<in> (ts lxs t) . \<not> (\<exists> wm \<in> ws lxs t . t' \<le> wm)}"

lemma coll_diff_head:
  "lhd' lxs = Some (Data t' d) \<Longrightarrow>
   t \<noteq> t' \<Longrightarrow>
   coll lxs t = coll (ltl lxs) t"
  apply (simp add: coll_def)
  by (smt (verit, ccfv_SIG) event.simps(5) lfilter_LCons lhd'_def lhd_LCons_ltl option.distinct(1) option.sel)

lemma coll_eq_coll_ltl:
  "monotone lxs WM \<Longrightarrow>
   productive lxs \<Longrightarrow>
   coll (LCons (Data t d) lxs) t = add_mset d (coll lxs t)"
  apply (simp add: coll_def)
  apply (cases "lfinite lxs")
   apply (simp add: map_filter_simps(1))
  apply (subst list_of_LCons_conv)
  apply (simp add: map_filter_simps strict_monotone_productive_lfinite_lfilter_eq_t)
  done

lemma coll_eq_coll_ltl_Watermark[simp]:
  "coll (LCons (Watermark wm) lxs) t = coll lxs t"
  apply (simp add: coll_def)
  done

lemma sum_coll_ltl:
  "finite A \<Longrightarrow>
   t \<in> A \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   productive lxs \<Longrightarrow>
   sum (coll (LCons (Data t d) lxs)) A = sum (coll lxs) A + {#d#}"
  apply (induct A arbitrary: lxs rule: finite.induct)
   apply fastforce
  subgoal for A a ws
    apply (cases "a \<in> A")
     apply (simp add: insert_absorb)
    apply (subst (1 2) comm_monoid_add_class.sum.insert)
      apply assumption+
    apply (smt (verit, best) add.commute add_mset_add_single coll_diff_head coll_eq_coll_ltl insertE lhd'_simps(2) ltl_simps(2) sum.cong union_mset_add_mset_right)
    done
  done

lemma sum_coll_ltl_not_in:
  "finite A \<Longrightarrow>
   t \<notin> A \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   productive lxs \<Longrightarrow>
   sum (coll (LCons (Data t d) lxs)) A = sum (coll lxs) A"
  apply (induct A arbitrary: lxs rule: finite.induct)
   apply fastforce
  subgoal for A a ws
    apply (cases "a \<in> A")
     apply (simp add: insert_absorb)
    apply (subst (1 2) comm_monoid_add_class.sum.insert)
      apply assumption+
    apply (metis coll_diff_head insertCI lhd'_simps(2) ltl_simps(2))
    done
  done

lemma not_in_ts_coll_empty:
  "finite (ts lxs wm) \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   productive lxs \<Longrightarrow>
   t \<notin> ts lxs wm \<Longrightarrow>
   t \<le> wm \<Longrightarrow>
   \<exists>wm'\<ge>wm. Watermark wm' \<in> lset lxs \<Longrightarrow>
   coll lxs t = {#}"
  apply (subgoal_tac "lfinite (lfilter (\<lambda>x. case x of Data t' d \<Rightarrow> t' = t | Watermark wm \<Rightarrow> False) lxs)")
   defer
  using strict_monotone_productive_lfinite_lfilter_eq_t apply blast
  unfolding coll_def list_of_def
  apply simp
  apply (smt (verit, best) diverge_lfilter_LNil event.split_sel le_boolE list_of_LNil list_of_def map_filter_simps(2) mem_Collect_eq min_def ts_def)
  done

lemma ts_all_not_le:
  "monotone (LCons (Watermark wm) lxs) WM \<Longrightarrow>
   \<exists>wm\<ge>t. Watermark wm \<in> lset lxs \<Longrightarrow>
   (\<forall>x\<in>ts lxs t. \<not> x \<le> wm)"
  apply (erule monotone.cases)
    apply simp_all
  unfolding ts_def
  apply safe
  apply (meson Data_set_strict_monotone_not_GE insertI1)
  done

lemma coll_diff_head_2:
  "t \<noteq> t' \<Longrightarrow>
   coll (LCons (Data t' d) lxs) t = coll lxs t"
  unfolding coll_def
  apply simp
  done

fun ltaken_Data :: "nat \<Rightarrow> _ llist \<Rightarrow> _ list" where
  "ltaken_Data (Suc n) (LCons (Watermark _) lxs) = ltaken_Data n lxs"
| "ltaken_Data (Suc n) (LCons (Data t batch) lxs) = (t, batch) # ltaken_Data n lxs"
| "ltaken_Data _ _ = []"

lemma ltaken_Data_0[simp]:
  "ltaken_Data 0 lxs = []"
  apply (cases lxs)
   apply simp_all
  done

lemma ltaken_Data_LCons_Watermark:
  "ltaken_Data n (LCons (Watermark wm) lxs) = ltaken_Data (n - 1) lxs"
  apply (induct n arbitrary: lxs wm)
   apply simp_all
  done


definition coll_list :: "('t::order \<times> 'd) list \<Rightarrow> 't \<Rightarrow> _ list" where
  "coll_list xs t = map snd (filter (((=) t) \<circ> fst) xs)"

lemma coll_list_append[simp]:
  "coll_list (xs@ys) t = coll_list xs t @ coll_list ys t"
  unfolding coll_list_def
  apply force
  done

lemma coll_list_nil[simp]:
  "coll_list [] t = []"
  unfolding coll_list_def
  apply simp
  done

abbreviation incr_coll_list :: "('t::order \<times> 'd) list \<Rightarrow> 't \<Rightarrow> 'd list" where
  "incr_coll_list xs t \<equiv> map snd (filter (((\<le>) t) \<circ> fst) xs)"

definition ps where
  "ps A (t::_::order) = {t' \<in> A. t' < t \<and> (\<forall> t'' \<in> {t' \<in> A. t' < t}. \<not> t'' > t')}"

function incr_paths_mset :: "('t::order) list \<Rightarrow> 't \<Rightarrow> _ multiset" where
  [simp del]: "incr_paths_mset xs t = (mset_set (ps (set xs) t) + sum (incr_paths_mset (filter ((>) t) xs)) (ps (set xs) t))"
   apply fast+
  done
termination
  apply (relation "measures [\<lambda> (xs, t) . length (filter ((>) t) xs)]")
   apply auto[1]
  apply (auto simp add: ps_def)
  by (metis filter_filter filter_set length_filter_less member_filter)

term Zorn.pred_on.maxchain
definition paths :: "('a::order) set \<Rightarrow> 'a \<Rightarrow> 'a set set" where
  "paths A t = {a \<in> Pow {t' \<in> A . t' < t} . Zorn.pred_on.maxchain {t' \<in> A . t' < t} (<) a}"

definition
  "filter_chains xs = filter (\<lambda> l . (\<forall> (e1::_::order) \<in> (set l). (\<forall> e2 \<in> (set l). e1 < e2 \<or> e2 < e1 \<or> e1 = e2))) xs"

definition 
  "filter_max_chains xs = filter (\<lambda> l . \<forall> l' \<in> set xs . \<not> (set l) \<subset> (set l')) xs"

lemma filter_max_chains_sub_filter_chains:                  
  "set (filter_max_chains xs) \<subseteq> set xs"
  unfolding filter_max_chains_def
  apply (meson filter_is_subset)
  done

lemma filter_chains_subset:
  "set (filter_chains xs) \<subseteq> set xs"
  unfolding filter_chains_def
  apply auto
  done

lemma filter_max_chains_is_chain:
  "x \<in> set ` set (filter_max_chains (filter_chains (List.subseqs xs))) \<Longrightarrow> Zorn.pred_on.chain ((set xs)) (<) x"
  unfolding filter_max_chains_def
  apply (induct xs arbitrary: x)
   apply (simp add: Collect_conv_if pred_on.chain_def pred_on.maxchain_def paths_def filter_chains_def)
  apply (auto simp add: remove_def Collect_conv_if pred_on.chain_def pred_on.maxchain_def paths_def filter_chains_def Let_def)
  apply (meson subseq_order.dual_order.trans subseq_singleton_left)
  by (meson subseq_order.dual_order.trans subseq_singleton_left)

lemma chain_in_subseqs:
  "Zorn.pred_on.chain ((set xs)) (<) A \<Longrightarrow> A \<in> set ` set (List.subseqs xs)"
  apply (induct xs arbitrary: A)
   apply (simp add: filter_max_chains_def Collect_conv_if pred_on.chain_def pred_on.maxchain_def paths_def filter_chains_def)
  apply (simp add: subset_insert_iff filter_max_chains_def Collect_conv_if pred_on.chain_def pred_on.maxchain_def paths_def filter_chains_def Let_def split: if_splits)
   apply (elim conjE disjE)
   apply (metis Diff_single_insert Pow_iff list.set_map list.simps(15) set_append subseqs.simps(2) subseqs_powset)
  apply (metis Un_iff image_Un)
  done

lemma maxchain_in_subseqs:
  "Zorn.pred_on.maxchain (set xs) (<) A \<Longrightarrow> A \<in> set ` set (List.subseqs xs)"
  using chain_in_subseqs pred_on.maxchain_imp_chain by blast

lemma chain_in_filter_chains:
  "Zorn.pred_on.chain (set xs) (<) A \<Longrightarrow> A \<in> set ` set (filter_chains (List.subseqs xs))" 
  apply (subgoal_tac "A \<subseteq> set xs")
  defer
  apply (simp add: pred_on.chain_def)
  apply (frule chain_in_subseqs)
  unfolding filter_chains_def
  apply auto
  apply hypsubst_thin
  subgoal for A
  apply (induct xs arbitrary: A)
   apply (simp add: filter_max_chains_def Collect_conv_if pred_on.chain_def pred_on.maxchain_def paths_def filter_chains_def)
    using list_emb_Nil2 apply fastforce
    apply auto
    apply (simp add: subset_insert_iff filter_max_chains_def Collect_conv_if pred_on.chain_def pred_on.maxchain_def paths_def filter_chains_def Let_def split: if_splits)
    subgoal for a xs A
      apply (drule meta_spec[of _ "filter ((\<noteq>) a) A"])
      apply (drule meta_mp)
       apply auto
      apply (drule meta_mp)
      apply auto
      apply (drule meta_mp)
      apply (smt (verit, ccfv_SIG) filter.simps(2) list.sel(3) list_emb.simps nth_Cons_0 subseq_filter_left subseq_order.dual_order.trans)
      apply auto
      done
    apply fast
    done
  done

lemma maxchain_in_filter_chains:
  "Zorn.pred_on.maxchain ((set xs)) (<) A \<Longrightarrow> A \<in> set ` set (filter_chains (List.subseqs xs))" 
  using chain_in_filter_chains pred_on.maxchain_imp_chain by blast

lemma filter_subseqs_powset:
  "set ` set (filter (\<lambda> l. P (set l)) (subseqs xs)) = {x \<in> Pow (set xs) . P x}"
  by (smt (verit) Collect_cong image_iff set_filter setcompr_eq_image subseqs_powset)

lemma maxchain_in_filter_max_chains:
  "Zorn.pred_on.maxchain (set xs) (<) A \<Longrightarrow> (A::_::order set) \<in> set ` set (filter_max_chains (filter_chains (List.subseqs xs)))"
  unfolding filter_max_chains_def filter_chains_def
  apply (simp only: filter_filter)
  apply (subst filter_subseqs_powset)
  apply (frule maxchain_in_subseqs)
  apply (frule maxchain_in_filter_chains)
  unfolding Zorn.pred_on.maxchain_def pred_on.chain_def
  apply (induct xs arbitrary: A)
   apply (simp add: filter_max_chains_def Collect_conv_if pred_on.chain_def pred_on.maxchain_def paths_def filter_chains_def)
  apply (simp add: Let_def)
  apply safe
       apply (metis dual_order.refl)
      apply (metis Pow_iff Set.insert_mono image_eqI list.simps(15) psubsetI subseqs_powset)
     apply (metis insert_iff psubsetI subseq_order.dual_order.trans subseq_singleton_left subsetI)
    apply force
   apply (metis Pow_iff Set.insert_mono image_eqI list.simps(15) psubsetI subseqs_powset)
  apply (metis insert_iff psubsetI subseq_order.dual_order.trans subseq_singleton_left subsetI)
  done

lemma filter_max_chains_is_chain_alt:
  "x \<in> set (filter_max_chains (filter_chains (List.subseqs xs))) \<Longrightarrow> Zorn.pred_on.chain ((set xs)) (<) (set x)"
  by (simp add: filter_max_chains_is_chain)

definition paths_from_list :: "('a::order) list \<Rightarrow> 'a \<Rightarrow> 'a list list" where
  "paths_from_list xs t = (
    let less = filter ((>) t) xs in
    let subs = List.subseqs less in
    let maxs = filter_chains subs in
    filter_max_chains maxs
   )"

find_theorems List.subseqs name: simps

lemma paths_from_list_soundness:
  "set ` (set (paths_from_list xs t)) \<subseteq> paths (set xs) t"
  apply safe
  subgoal for _ x
    unfolding paths_from_list_def Let_def paths_def
    apply (smt (verit, ccfv_SIG) Collect_cong chain_in_filter_chains chain_in_subseqs filter_max_chains_def filter_max_chains_is_chain_alt image_iff mem_Collect_eq pred_on.maxchain_def set_filter subseqs_powset)
    done
  done

lemma paths_from_list_completeness:
  "paths (set xs) t \<subseteq> set ` (set (paths_from_list xs t))"
  apply safe
  subgoal
    unfolding paths_from_list_def Let_def paths_def
    apply (metis (no_types, lifting) Collect_cong maxchain_in_filter_max_chains mem_Collect_eq set_filter)
    done
  done

lemma paths_from_list_correctness:
  "set ` (set (paths_from_list xs t)) = paths (set xs) t"
  by (simp add: Orderings.order_eq_iff paths_from_list_completeness paths_from_list_soundness)

definition multi_incr_coll_list :: "'t \<Rightarrow> ('t::order \<times> 'd) list \<Rightarrow> _" where
  "multi_incr_coll_list t xs = 
   mset (concat (map (\<lambda> x . concat (map (\<lambda> t' . coll_list xs t') x)) (paths_from_list (remdups (map fst xs)) t))) +
   mset (coll_list xs t)"

lemma incr_paths_append_mset_comm:
  "incr_paths_mset (ys@xs) t = incr_paths_mset (xs@ys) t"
  apply (induct "ys@xs" t arbitrary: xs ys rule: incr_paths_mset.induct)
  apply (subst (1 2) incr_paths_mset.simps)
  apply auto
  subgoal for t xs ys
    apply (subgoal_tac 
        "{t'. (t' \<in> set ys \<or> t' \<in> set xs) \<and> t' < t \<and> (\<forall>t''. (t'' \<in> set ys \<or> t'' \<in> set xs) \<and> t'' < t \<longrightarrow> \<not> t' < t'')} = 
     {t'. (t' \<in> set xs \<or> t' \<in> set ys) \<and> t' < t \<and> (\<forall>t''. (t'' \<in> set xs \<or> t'' \<in> set ys) \<and> t'' < t \<longrightarrow> \<not> t' < t'')}")
     defer
     apply blast
    apply (auto simp add: ps_def)
    done
  done

lemma distinct_List_subseqs:
  "distinct xs \<Longrightarrow>
   distinct (List.subseqs xs)"
  apply (induct xs)
   apply auto
  unfolding Let_def 
  apply simp
  apply safe
   apply (simp add: distinct_map)
  using list_emb_set apply fastforce
  done

lemma distinct_paths_from_list:
  "distinct xs \<Longrightarrow>
   distinct (paths_from_list xs t)"
  unfolding paths_from_list_def Let_def filter_max_chains_def filter_chains_def
  apply (meson distinct_List_subseqs distinct_filter)
  done

abbreviation "multi_incr_ts_mset A t \<equiv> sum mset_set (paths A t)"

definition "multi_incr_coll_llist lxs t =
 List.map_filter (\<lambda> e . case e of Watermark _ \<Rightarrow> None | Data t d \<Rightarrow> Some (t, d)) (list_of (lfilter (\<lambda> ev . case ev of Watermark _ \<Rightarrow> False | Data t' d \<Rightarrow> t' \<le> t) lxs))"

definition "multi_incr_coll_mset lxs t = sum (sum (coll lxs)) (paths (ts lxs t) t) + coll lxs t"

lemma le_paths_eq:
  "{a \<in> A . a \<le> (t::_::order)} = {b \<in> B . b \<le> t} \<Longrightarrow>
   paths A t = paths B t"
  unfolding paths_def 
  apply simp
  apply (smt (verit, best) Collect_cong Collect_mono_iff order_less_imp_le)
  done

lemma sync_ts_leq_in_lset:
  "t' \<in> (sync_ts lxs t) \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   \<exists> wm \<ge> t. Watermark wm \<in> lset lxs \<Longrightarrow>
   t' \<in> tmp ` lset lxs \<and> t' \<le> t"
  unfolding sync_ts_def ts_def
  using image_iff apply fastforce
  done

abbreviation
  "EV_LE_WM wm ev \<equiv> (case ev of Watermark wm' \<Rightarrow> False | Data t d \<Rightarrow> t \<le> wm)"

definition
  "incr_coll lxs wm = List.map_filter (\<lambda> e . case e of Watermark _ \<Rightarrow> None | Data t d \<Rightarrow> Some (t, d))
    (list_of (lfilter (EV_LE_WM wm)lxs))"

abbreviation
  "EV_EX_WS lxs wm e \<equiv> case e of Data t d \<Rightarrow> \<not> (\<exists> wm' \<in> ws lxs wm . t \<le> wm') | Watermark _ \<Rightarrow> False"

abbreviation
  "get_Data e \<equiv> case e of Data t d \<Rightarrow> Some d | Watermark _ \<Rightarrow> None"

lemma ltaken_Data_in_Suc:
  "x \<in> set (ltaken_Data n lxs) \<Longrightarrow>
   n \<le> m \<Longrightarrow>
   x \<in> set (ltaken_Data m lxs)"
  apply (induct n arbitrary: m lxs)
   apply auto
  subgoal for n m lxs
    apply (cases lxs)
     apply auto
    subgoal for x lxs'
      apply (cases x)
       apply auto
      using Suc_le_D apply fastforce
       apply (cases m)
        apply (auto simp add: ltaken_Data_LCons_Watermark)
      done
    done
  done

lemma in_ts_strict_monotone_False:
  "monotone (LCons (Watermark wm) lxs) WM \<Longrightarrow>
   t \<in> ts lxs wm \<Longrightarrow>
   False"
  unfolding ts_def
  using Data_tail_ahead_of_t apply fastforce
  done

lemma in_ts_LCons_Data_cases:
  "t \<in> ts (LCons (Data t' d) lxs) wm \<Longrightarrow>
   t \<in> ts lxs wm \<or> t = t'"
  unfolding ts_def
  apply auto
  done


lemma sync_ts_subset_ts:
  "sync_ts lxs wm \<subseteq> ts lxs wm"
  unfolding sync_ts_def ts_def
  apply auto
  done

lemma in_ts_transitive:
  "x \<in> ts lxs t \<Longrightarrow>
   t \<in> ts lxs wm \<Longrightarrow>
   x \<in> ts lxs wm"
  unfolding ts_def
  apply auto
  done

lemma ts_le:
  "t' \<in> ts lxs t \<Longrightarrow>
   t' \<le> t"
  unfolding ts_def
  apply auto
  done

lemma ts_le_2:
  "t' \<in> ts lxs t \<Longrightarrow>
   t \<le> wm \<Longrightarrow>
   t' \<in> ts lxs wm"
  unfolding ts_def
  apply auto
  done

lemma ldropn_LCons_ltaken_Data:
  "\<exists>n'\<le>n. ldropn n' lxs = LCons (Data wm batch) lxs' \<Longrightarrow> 
  (wm, batch) \<in> set (ltaken_Data (Suc n) lxs)"
  apply (induct "Suc n" lxs arbitrary: n rule: ltaken_Data.induct)
    apply auto
    apply (metis (no_types, lifting) diff_is_0_eq' diff_le_self event.distinct(1) gr0_conv_Suc ldropn_0 ldropn_Suc_LCons llist.inject not_less_eq_eq order.order_iff_strict)
   apply (metis (no_types, lifting) diff_is_0_eq' diff_le_self event.inject(1) gr0_conv_Suc ldropn_0 ldropn_Suc_LCons llist.inject not_less_eq_eq order.order_iff_strict)+
  done

lemma in_ltaken_Data_ldropn_LCons:
  "(wm, batch) \<in> set (ltaken_Data (Suc n) lxs) \<Longrightarrow> \<exists>n'\<le>n. \<exists>lxs'. ldropn n' lxs = LCons (Data wm batch) lxs'"
  apply (induct "Suc n" lxs arbitrary: n rule: ltaken_Data.induct)
    apply auto
   apply (metis (no_types, opaque_lifting) Suc_less_eq dual_order.strict_trans2 empty_iff empty_set gr0_conv_Suc ldropn_Suc_LCons lessI ltaken_Data_0 ltaken_Data_in_Suc not_less_eq_eq)
  apply (metis empty_iff empty_set ldropn_Suc_LCons ltaken_Data_0 not0_implies_Suc not_less_eq_eq)
  done

lemma timestamp_in_taken_Data_inversion_aux:
  "t \<in> fst ` (\<Union>a\<in>set (ltaken_Data n lxs). set (snd a)) \<Longrightarrow>
   \<exists> wm batch . (wm, batch) \<in> set (ltaken_Data n lxs) \<and> t \<in> fst ` set batch"
  apply (induct n arbitrary: lxs)
   apply auto
  subgoal for n lxs b aa ba
    apply (cases lxs)
     apply auto
    subgoal for x lxs'
      apply (cases x)
       apply auto
        apply (metis fst_conv imageI)+
      done
    done
  done

lemma ts_change_t:
  "t' \<le> t \<Longrightarrow>
   t' \<le> wm \<Longrightarrow>
   t' \<in> ts lxs t \<Longrightarrow>
   t' \<in> ts lxs wm"
  unfolding ts_def
  apply auto
  done

lemma ts_LCons:
  "t \<in> ts lxs wm \<Longrightarrow>
   t \<in> ts (LCons (Data t' d) lxs) wm"
  unfolding ts_def
  apply auto
  done

lemma in_ts_LCons_LE:
  "t \<le> wm \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   \<exists> wm' \<ge> wm . Watermark wm' \<in> lset lxs \<Longrightarrow>
   t \<in> ts (LCons (Data t d) lxs) wm"
  unfolding ts_def
  apply auto
  done

lemma coll_list_concat_ltaken_Data_Nil:
  "\<not> (\<exists> wm d . Data wm d \<in> lset lxs \<and> t \<in> fst ` set d) \<Longrightarrow>
   coll_list (concat (map snd (ltaken_Data n lxs))) t = []"
  apply (induct n arbitrary: lxs)
   apply simp
  subgoal for n lxs
    apply (cases lxs)
     apply auto
    subgoal for x lxs'
      apply (cases x)
      unfolding coll_list_def
       apply auto
      apply (smt (z3) comp_apply filter_False image_iff)
      done
    done
  done

lemma coll_empty:
  "\<not> (\<exists> d . Data t d \<in> lset lxs) \<Longrightarrow>
   coll lxs t = {#}"
  unfolding coll_def
  apply (smt (verit) dual_order.refl event.split_sel le_boolD lfilter_empty_conv list_of_LNil map_filter_simps(2) mset_zero_iff nless_le)
  done

lemma coll_LCons_coll_List:
  "\<exists> wm \<ge> t . Watermark wm \<in> lset lxs \<Longrightarrow>
   monotone lxs WM \<Longrightarrow>
   coll (LCons (Data t' d) lxs) t = coll lxs t + mset (coll_list [(t', d)] t)"
  unfolding coll_def coll_list_def
  apply (auto simp add: map_filter_simps)
  apply (smt (verit, best) event.case_eq_if event.simps(5) lfilter_cong list_of_LCons map_filter_simps(1) mset.simps(2) option.case(2) strict_monotone_lfinite_lfilter_eq_t_alt)
  done

lemma in_paths_in_set:
  "x \<in> paths A t \<Longrightarrow>
   \<forall> t' \<in> x . t' \<in> A"
  unfolding paths_def
  apply auto
  done

lemma paths_from_list_distinct_lists:
  "distinct xs \<Longrightarrow>
   x \<in> set (paths_from_list xs t) \<Longrightarrow>
   y \<in> set (paths_from_list xs t) \<Longrightarrow>
   x \<noteq> y \<Longrightarrow>
   set x \<noteq> set y"
  apply (induct xs)
   apply (auto simp add: paths_from_list_def filter_max_chains_def filter_chains_def)[1]
   apply (smt (z3) equals0D filter.simps(1) list.inject list.set_cases set_empty2)
  subgoal for x xs
    unfolding  paths_from_list_def filter_max_chains_def filter_chains_def Let_def
    apply (simp split: if_splits)
    apply safe
    apply (smt (verit, ccfv_SIG) distinct.simps(2) distinct_filter filter_cong filter_in_nths filter_set member_filter subseq_conv_nths)
    done
  done

lemma set_paths_from_list_card_preserves:
  "card (set (paths_from_list (remdups xs) t)) = card (set ` set (paths_from_list (remdups xs) t))"
  apply (subst card_image)
   apply auto[2]
  apply (meson distinct_remdups inj_onI paths_from_list_distinct_lists)
  done

lemma mset_multi_incr_coll_list_eq_multi_incr_coll_mset:
  "ts lxs t = {t' \<in> fst ` set xs . t' \<le> t} \<Longrightarrow>
   \<forall> t' \<in> {t' \<in> fst ` set xs . t' \<le> t} . coll lxs t' = mset (coll_list xs t') \<Longrightarrow>
   multi_incr_coll_list t xs = multi_incr_coll_mset lxs t"
  unfolding multi_incr_coll_list_def multi_incr_coll_mset_def
  apply (subst mset_concat)
  apply (subst map_map)
  apply (subst sum_list_distinct_conv_sum_set)
   apply (simp add: distinct_paths_from_list)
  apply simp
  apply (subst mset_concat)
  apply (subst map_map)
  apply (subst Sum_set_sum_list_map_Sum_sum_set)
  subgoal
    apply auto
    apply (metis (no_types, lifting) distinct_filter distinct_remdups filter_chains_subset filter_max_chains_sub_filter_chains paths_from_list_def subseqs_distinctD subset_eq)
    done
  apply (subst sum_sum_change_fun[where g="mset \<circ> coll_list xs"])
  subgoal 
    apply safe
    apply (drule in_paths_in_set)
    apply (smt (verit, ccfv_threshold) comp_apply image_iff mem_Collect_eq sum_change_fun)
    done
  apply (subst Sum_sum_sum_sum)
   apply (simp add: set_paths_from_list_card_preserves)
  apply (simp add: paths_from_list_correctness)
  apply (rule cong[where f="\<lambda> x . sum (sum (\<lambda>x. mset (coll_list xs x))) (paths (fst ` set xs) t) + x" and
   g="\<lambda> x . sum (sum (\<lambda>x. mset (coll_list xs x))) (paths {t' \<in> fst ` set xs. t' \<le> t} t) + x"])
   apply (metis (mono_tags, lifting) Collect_cong le_paths_eq mem_Collect_eq)
  apply (cases "t \<in> fst ` set xs")
  subgoal
  apply (drule spec[of _ t])
  apply (drule mp)
   apply auto
    done
  unfolding coll_def coll_list_def ts_def
  apply auto
  apply (subgoal_tac "t \<notin> {t'. (\<exists>d'. Data t' d' \<in> lset lxs) \<and> t' \<le> t}")
   defer
  apply blast
  apply (subgoal_tac "lfilter (\<lambda>x. case x of Data t' d \<Rightarrow> t' = t | Watermark wm \<Rightarrow> False) lxs = LNil")
  defer
   apply (smt (verit) diverge_lfilter_LNil dual_order.refl event.split_sel le_boolD mem_Collect_eq nless_le)
  apply simp
  apply (smt (verit, del_insts) filter_False image_iff image_mset_is_empty_iff map_filter_simps(2) mset.simps(1) mset_filter)
  done

lemma img_tmp_Lambda_Data:
  "finite A \<Longrightarrow> tmp ` (\<lambda>x. Data x (f x)) ` A = A"
  apply (induct A rule: finite_induct)
  apply auto
  done

find_theorems lfilter  lfinite

(*
- Completeness (DONE)
- Clean up proofs (use unused_thms ) (DONE)
- productive and monotone of multi_incr_op and multi_incr_hist_op (DONE)
- replace ts by ts' (DONE)
- Modify op to always output a list (DONE)
- End-of-stream op component (In progress)
- remove productive assumption from soundness and monotone proofs 
- Multiple inputs
  -- time-aware join (window join)
     -- use building blocks
  -- correctness proofs
- Applications/more examples - Use partial order
- Write optmized hist_op in total order that is equal to the total order instance of multi_incr_hist_op
- Cycles
- synced_coll_op as flat_map
- Re-write proofs in isar
*)

(*
  Paper Schedule:
  Draft Section 2: 15/09
  Revision Section 3: 15/09
  Draft Section 4: 22/09
  Revision Section 2: ?
  Draft Section 5: 02/10
  Revision Section 4: ?
  Draft Section 1 and 6: 06/10
  Revision Section 5: ?
  Revision Section 1 and 6: ?

  Isabelle Schedule:
  -- Multiple inputs

*)

(*
 Contributions:
- Verified time-aware stream processing
- Formally verified Time aware lazy list processing
  -- monotone
  -- productive
  -- Partially ordered timestmaps
- Multiple inputs
- Building blocks
- reasoning by coinduction to prove equivalence of logics
  -- example: optmized hist_op in total order that is equal to the total order instance of multi_incr_hist_op
- Stateful operators
- Mixed co-recursion and monadic recursion 
- Proof methodology (skip_n generalization, coinduction generalization)
- Examples: partial ordered incremental computation, so on


Sections:
1. Introduction
   -- Contributions
2. Related work
   -- Stream processing (frameworks): Flink, Timely...
   -- https://link.springer.com/chapter/10.1007/978-3-030-44914-8_15
   -- Modeling stream processing
      -- Stream processors in Isabelle (Representation of stream processors using nested fixed points)
   -- Careful study for formalization of stream processing
      -- Map reduce verified in proof assistant (iris)
      -- Tiny formalization of stream processors
3. Preliminaries:
    Codatypes (lazy lists), coinductive command (lprefix), co-recursive (lappend), lshift (friend), partial_function (lfilter) and ccpo llist.
4. Lazy Lists processors:
   -- op co-datatype
      -- link with stream processing operators
   -- produce_inner (ccpo)
   -- produce (corec)
   -- compose_op + correctness (motivate skip_n_productions)
   -- skip_n_productions (correctness)
5. Time-Aware Operators
   -- strict monotone
   -- productive 
      -- first coinductive one
      -- second present the ltl
   -- show preservation of productive and strict monotone for compose_op and skip_n_productions_op
   -- sync_op and coll_synced_op
   -- correctness
      - soundness
      - monotone
      - productive 
      - completeness
   -- compositional reasoning
      -- multi_incremental
6. Case study
    -- Histograms
      -- optimized for linear order (and equality)
    -- Binary operator

*)

end
