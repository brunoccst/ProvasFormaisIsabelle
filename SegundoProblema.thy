theory SegundoProblema
imports Main
begin 

(* Definindo a funcao fataux *)
primrec fataux::"nat \<Rightarrow> nat \<Rightarrow> nat"
  where
    fataux01:"fataux 0 cont = cont" |
    fataux02:"fataux (Suc n) cont = fataux n (( Suc n) * cont)"

(* Testando fataux com valores *)
value "fataux 4 1"

(* Provando fataux *)
theorem fataux:"\<forall>cont. fataux (Suc n) cont = fataux n ((Suc n)*cont)"
proof(induct n)

(* Iniciando a prova pelo primeiro subgoal - provar para caso base *)
show " \<forall>cont. fataux (Suc 0) cont = fataux 0 (Suc 0 * cont)"
proof (rule allI)
  fix cont0::nat  
  have "fataux (Suc 0) cont0 = fataux 0 ((Suc 0) * cont0 )  " by (simp only:fataux02)
  also have "... = ((Suc 0) * cont0) " by (simp only:fataux01)
  also have "... = cont0" by arith
  also have "... = fataux 0 ((Suc 0) * cont0)" by(simp only:fataux01)
  finally show "fataux (Suc 0) cont0 = fataux 0 ((Suc 0) * cont0)" by simp
qed

(* Continuando a prova pelo segundo subgoal - provar para n+1 *)
next
fix m0::nat
assume HI:"\<forall>cont. fataux (Suc m0) cont = fataux m0 ((Suc m0) * cont)"
show "\<forall>cont. fataux (Suc(Suc m0)) cont = fataux (Suc m0) ((Suc (Suc m0))*cont)"
proof (rule allI)
  fix a0::nat
  have "fataux (Suc(Suc m0)) a0 = fataux (Suc m0) ((Suc (Suc m0)) * a0) " by (simp only:fataux02)
  also have "... = " by (simp)
  print_state






