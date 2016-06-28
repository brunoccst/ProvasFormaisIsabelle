theory Somatorio
imports Main
begin

(* Definindo a funcao recursiva na cauda somaux *)
primrec somaux::"nat \<Rightarrow> nat \<Rightarrow> nat"
  where
    somaux01:"somaux 0 cont = cont" |
    somaux02:"somaux (Suc n) cont = somaux n (( (Suc n) * (Suc n) ) + cont)"

(* Definindo a funcao nao recursiva na cauda somatorio *)
fun somatorio::"nat \<Rightarrow> nat" where
	somatorio01:"somatorio n = somaux n 0"

(* Testando a funcao somatorio *)
value "somatorio 3"

(* Provando o teorema com invariante *)
theorem th01:"\<forall>a. somaux n a = (\<Sum>i=1..n. i*i) + a"
apply(induction n)
apply(simp)
apply(simp)
done

(* Provando o teorema para somaux *)
theorem th02:"\<forall>a. somaux n a = (\<Sum>i=1..n. i*i) + a"
proof(induction n)

(* Provando para o caso base *)
show"\<forall>a. somaux 0 a = (\<Sum>i=1..0. i*i) + a"
proof(rule allI)
  fix a0::nat
  have "somaux 0 a0 = a0" by(simp only:somaux01)
  also have "... = (\<Sum>i=1..0. i*i) + a0" by (simp)
  finally show "somaux 0 a0 = (\<Sum>i=1..0. i*i) + a0" by (simp)
qed

(* Provando para n + 1 *)
next
fix x0::nat
assume HI:"\<forall>a. somaux x0 a = (\<Sum>i=1..x0. i*i) + a"
show"\<forall>a. somaux (Suc x0) a = (\<Sum>i=1..(Suc x0). i*i) + a"
proof(rule allI)
  fix a0::nat
  have "somaux (Suc x0) a0 = somaux x0 ((Suc x0)*(Suc x0)+a0)" by (simp only:somaux02)
  also have "... = (\<Sum>i=1..x0. i*i) + (Suc x0)*(Suc x0)+a0" by (simp only:HI)
  also have "... = (\<Sum>i=1..(Suc x0). i*i) + a0" by (simp)
  finally show "somaux (Suc x0) a0 =(\<Sum>i=1..(Suc x0). i*i) + a0" by (simp)
qed
qed

(* Provando teorema para somatorio *)
theorem th03:"somatorio n = (\<Sum>i=1..n. i*i)"
proof(induction n)

(*  Provando para o caso base *)
show"somatorio 0 = (\<Sum>i=1..0. i*i)"
proof -
  have "somatorio 0 = somaux 0 0" by (simp only:somatorio01)
  also have "... = 0" by (simp only:somaux01)
  finally show "somatorio 0 = (\<Sum>i=1..0. i*i)" by(simp)
qed

(* Provando para n + 1 *)
next
fix n0::nat
assume HI: "somatorio n0 = (\<Sum>i=1..n0. i*i)"
show"somatorio (Suc n0) = (\<Sum>i=1..(Suc n0). i*i)"
proof -
  have "somatorio (Suc n0) = somaux (Suc n0) 0" by (simp only:somatorio01)
  also have "... = (\<Sum>i=1..(Suc n0). i*i) + 0" by (simp only:th01)
  finally show "somatorio (Suc n0) = (\<Sum>i=1..(Suc n0). i*i)" by(simp)
qed
qed

end