theory SegundoProblema
imports Complex_Main
begin 

(* Funcao fatorial nao-recursiva na cauda *)
fun factorial::"nat \<Rightarrow> nat"
  where
    factorial01:"factorial 0 = 1"
    | factoria02:"factorial (Suc n) = (Suc n) * factorial (n)"

(* Definindo a funcao fataux *)
primrec fataux::"nat \<Rightarrow> nat \<Rightarrow> nat"
  where
    fataux01:"fataux 0 cont = cont" |
    fataux02:"fataux (Suc n) cont = fataux n (( Suc n) * cont)"

(* Testando fataux com valores *)
value "fataux 3 1"

(* Provando fataux *)
theorem th01:"\<forall>cont. fataux n cont = factorial n * cont"
proof(induct n)

(* Iniciando a prova pelo primeiro subgoal - provar para caso base *)
show "\<forall>cont. fataux 0 cont = factorial 0 * cont"
proof (rule allI)
  fix cont0::nat  
  have "fataux (Suc 0) cont0 = fataux 0 ((Suc 0) * cont0 )  " by (simp only:fataux02)
  also have "... = ((Suc 0) * cont0) " by (simp only:fataux01)
  also have "... = cont0" by arith
  also have "... = 1 * cont0" by arith
  finally show "fataux 0 cont0 = factorial 0 * cont0" by simp
qed

(* Continuando a prova pelo segundo subgoal - provar para n+1 *)
next
fix m0::nat
assume HI:"\<forall>cont. fataux m0 cont = factorial m0 * cont"
show "\<forall>cont. fataux (Suc m0) cont = factorial (Suc m0) * cont"
proof (rule allI)
  fix a0::nat
  have "fataux (Suc m0) a0 = fataux m0 ((Suc m0) * a0) " by (simp only:fataux02) 
  also have "... = factorial m0 * ((Suc m0) * a0)" by (simp only: HI)
  also have "... = factorial m0 * (Suc m0) * a0" by arith
  finally show "fataux (Suc m0) a0 = factorial (Suc m0) * a0" by simp
qed
qed





(* Definindo a funcao fat *)
fun fat::"nat \<Rightarrow> nat"
  where
    fat01:"fat 0 = 1" |
    fat02:"fat n = fataux n 1"

(* Testando a funcao fat *)
value "fat 3"

(* Provando fataux *)
theorem th02:"\<forall>cont. fat n = factorial n"
proof(induct n)

(* Iniciando a prova pelo primeiro subgoal - provar para caso base *)
show "\<forall>cont. fat 0 = factorial 0"
proof (rule allI)
  fix cont0::nat
  have "fat 0 = fataux 0 1" by (simp)
  also have "... = 1" by (simp)
  also have "... = factorial 0" by (simp add: th01)
  finally show "fat 0 = factorial 0" by (simp add: th01)
qed
next

(* Continuando a prova pelo segundo subgoal - provar para n+1 *)
fix m0::nat
assume HI:"\<forall>cont. fat m0 = factorial m0"
show "\<forall>cont. fat (Suc m0) = factorial (Suc m0)"
proof (rule allI)
  fix cont0::nat
  have "fat (Suc m0) = fataux (Suc m0) 1" by simp
  also have "... = factorial (Suc m0) * 1" by (simp add: th01)
  also have "... = factorial (Suc m0)" by arith
  finally show "fat (Suc m0) = factorial (Suc m0)" by arith
qed
qed

end
  
  
  