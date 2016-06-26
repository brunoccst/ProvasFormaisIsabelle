theory Multiplicacao
imports Main
begin

(* Definindo a funcao multacc *)
primrec multacc:: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
      where
        multacc01: "multacc 0 n a = a" |
        multacc02: "multacc (Suc(k)) n a = multacc k n (a+n)"

(* Testando valores de multacc *)
value "multacc 1 1 0"
value "multacc 2 2 0"

(* Provando multacc *)
theorem th01:"\<forall>y a::nat. multacc x y a = x * y + a"
proof(induct x)

(* Iniciando a prova pelo primeiro subgoal - provar para caso base *)
show "\<forall>y a::nat. multacc 0 y a = 0 * y + a"
proof (rule allI, rule allI)
  fix y0::nat
  fix a0::nat
  have "multacc 0 y0 a0 = 0 * y0 + a0" by (simp)
  also have "... = a0" by (simp only: multacc01)
  also have "... = (0 * y0) + a0" by arith
  also have "... = 0 * y0 + a0" by simp
  finally show "multacc 0 y0 a0 = 0 * y0 + a0" by simp
qed

(* Continuando a prova pelo segundo subgoal - provar para n+1 *)
next
fix x0::nat
assume HI:"\<forall>y a::nat. multacc x0 y a = x0 * y + a"
show "\<forall>y a. multacc (Suc x0) y a = (Suc x0) * y + a"
proof (rule allI, rule allI)
  fix y0::nat
  fix a0::nat
  have "multacc (Suc x0) y0 a0 = multacc x0 y0 (a0 + y0)" by (simp only: multacc02)
  also have "... = x0 * y0 + (a0 + y0)" by (simp only: HI) 
  also have "... = x0 * y0 + a0 + y0" by (arith) 
  also have "... = (x0 * y0) + (y0 * 1) + a0" by arith
  also have "... = (y0 * x0) + (y0 * 1) + a0" by algebra
  also have "... = y0 * (x0 + 1) + a0 " by algebra
  also have "... = (x0 + 1) * y0 + a0" by algebra
  finally show "multacc (Suc x0) y0 a0 = (Suc x0) * y0 + a0" by simp
qed
qed



(* Definindo a funcao mult *)
fun mult:: "nat \<Rightarrow> nat \<Rightarrow> nat"
  where
    mult01: "mult n m = multacc n m 0"

(* Testando valores com a funcao mult *)
value "mult 2 0"
value "mult 1 2"
value "mult 2 3"

(* Provando mult *)
theorem th02:"\<forall>y. mult x y = x * y"
proof(induct x)

(* Iniciando a prova pelo primeiro subgoal - provar para caso base *)
show "\<forall>y. mult 0 y = 0 * y"
proof (rule allI)
  fix y0::nat
  have "mult 0 y0 = multacc 0 y0 0" by (simp only: mult01)
  also have "... = 0" by (simp only: multacc01)
  also have "... = 0 * y0" by (arith)
  finally show "mult 0 y0 = 0 * y0" by (arith)
qed

(* Continuando a prova pelo segundo subgoal - provar para n+1 *)
next
fix x0::nat
assume HI:"\<forall>y. mult x0 y = x0 * y"
show "\<forall>y. mult (Suc x0) y = (Suc x0) * y"
proof (rule allI)
  fix y0::nat
  have "mult (Suc x0) y0 = multacc (Suc x0) y0 0" by (simp)
  also have "... = multacc x0 y0 (0 + y0)" by (simp only: multacc02)
  also have "... = multacc x0 y0 y0" by (simp)
  also have "... = x0 * y0 + y0" by (simp add: th01)
  also have "... = y0 * x0 + y0" by (algebra)
  also have "... = (y0 * x0) + (y0 * 1)" by (algebra)
  also have "... = y0 * (x0 + 1)" by (algebra)
  also have "... = (x0 + 1) * y0" by (algebra)
  also have "... = (Suc x0) * y0" by (simp)
  finally show "mult (Suc x0) y0 = (Suc x0) * y0" by (simp)
qed
qed

end