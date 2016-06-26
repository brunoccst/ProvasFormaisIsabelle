theory Multiplicacao
imports Main
begin

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







fun mult:: "nat \<Rightarrow> nat \<Rightarrow> nat"
  where
    mult01: "mult n 0 = multacc 0 n 0" |
    mult02: "mult n m = multacc n m 0"

theorem multAcc:"\<forall>x y. multacc(x y z) = x * y + z"

end

