theory TFAT
imports Complex_Main 
 
begin
primrec rec_nao_cald :: "'a list \<Rightarrow> nat" where
  rnc1: "rec_nao_cald [] = 0" |
  rnc2: "rec_nao_cald (h # l) = 1 + rec_nao_cald(l)" 
value "rec_nao_cald [1,2,3,6]"
theorem rec_nao_cald_theorem:"rec_nao_cald l = length l"
apply(induction l)
apply(simp)
apply(simp)
done
theorem len_nc:"rec_nao_cald l = length l"
proof(induct l)
	show"rec_nao_cald [] = length []"
	proof -
	have"rec_nao_cald [] = 0" by(simp only:rnc1)
	also have" ... = length[]" by(simp)
	finally show"rec_nao_cald [] = length []" by(simp)
qed
next
fix l0::"'a list" and e::'a
assume rec_nao_cald_hi: "rec_nao_cald l0 = length l0"
	show"rec_nao_cald (e#l0) = length (e#l0)"
	proof -
	have"rec_nao_cald (e#l0) = rec_nao_cald l0 + 1" by(simp only:rnc2)
	also have"... = length l0 + 1" by(simp only:rec_nao_cald_hi)
	also have"... = length (e#l0)" by(simp)
	finally show"rec_nao_cald (e#l0) = length (e#l0)" by(simp)
qed
qed
primrec rec_cald :: "'a list \<Rightarrow> nat \<Rightarrow> nat" where
  rc1: "rec_cald [] y = y" |
  rc2: "rec_cald (h # l) y = rec_cald (l) (Suc y)"
value "rec_cald [1,2] 0"
theorem rec_cald_inv:"\<forall>a. rec_cald l a = length l + a"
apply(induction l)
apply(simp)
apply(rule allI)
apply(simp)
done
theorem rec_cald_inv_test:"\<forall>a. rec_cald l a = length l + a"
proof(induction l)
	show"\<forall>a. rec_cald [] a = length [] + a"
	proof(rule allI)
	fix a0::nat
	have"rec_cald [] a0 = a0" by(simp only:rc1)
	also have"... = length [] + a0" by(simp)
	finally show"rec_cald [] a0 = length [] + a0" by(simp)
qed
next
fix l0::"'a list" and e::'a
assume rec_cald_inv_hi:"\<forall>a. rec_cald l0 a = length l0 + a"
	show"\<forall>a. rec_cald (e#l0) a = length (e#l0) + a"
	proof (rule allI)
	fix a0::nat
	have"rec_cald (e#l0) a0 = rec_cald l0 (Suc a0)" by(simp only:rc2)
	also have"... = length l0 + (Suc a0)" by(simp only:rec_cald_inv_hi)
	also have"... = length (e#l0) + a0" by(simp)
	finally show"rec_cald (e#l0) a0 = length (e#l0) + a0" by(simp)
qed
qed
theorem fun_igual_apply:"rec_nao_cald l = rec_cald l 0"
apply(induction l)
apply(simp)
apply(simp only:len_nc)
apply(simp only:rec_cald_inv_test)
done
theorem equi:"rec_nao_cald l = rec_cald l 0"
proof(induct l)
	show"rec_nao_cald [] = rec_cald [] 0"
	proof -
	have"rec_nao_cald [] = 0" by(simp only:rnc1)
	also have"... = rec_cald [] 0" by(simp)
	finally show"rec_nao_cald [] = rec_cald [] 0" by(simp)
	qed
next
fix l0::"'a list" and e::'a
assume"rec_nao_cald l0 = rec_cald l0 0"
	show"rec_nao_cald (e#l0) = rec_cald (e#l0) 0"
	proof -
	have"rec_nao_cald (e#l0) = length (e#l0)" by(simp only:len_nc)
	also have"... = rec_cald (e#l0) 0" by(simp only:rec_cald_inv_test)
	finally show"rec_nao_cald (e#l0) = rec_cald (e#l0) 0" by(simp)
qed
qed
end