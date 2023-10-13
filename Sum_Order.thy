section \<open>Pointwise order on sum types\<close>

theory Sum_Order
  imports 
    Main
begin

subsection \<open>Pointwise ordering\<close>

instantiation sum :: (ord, ord) ord
begin

inductive less_eq_sum :: "'a + 'b \<Rightarrow> 'a + 'b \<Rightarrow> bool" where
  Inl_leq: "t \<le> u \<Longrightarrow> less_eq_sum (Inl t) (Inl u)"
| Inr_leq: "t \<le> u \<Longrightarrow> less_eq_sum (Inr t) (Inr u)"

definition
  "(x::'a + 'b) < y \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x"

instance ..

end

instance sum :: (preorder, preorder) preorder
proof
  fix x y z :: "'a + 'b"
  show "x < y \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x"
    by (rule less_sum_def)
  show "x \<le> x"
    apply (cases x)
     apply (auto intro: less_eq_sum.intros)
    done

  assume "x \<le> y" and "y \<le> z" thus "x \<le> z"
    apply (cases x; cases y; cases z)
           apply (auto intro!: less_eq_sum.intros elim!: less_eq_sum.cases order_trans)
    done
qed

instance sum :: (order, order) order
  apply standard
  subgoal for x y
    apply (cases x; cases y)
       apply (auto intro!: antisym elim: less_eq_sum.cases)
    done
  done

end