theory ComprimentoDeLista
imports List
begin


(* Definindo a funcao recursiva na cauda auxiliar *)
primrec tail_len_c_aux::"'a list\<Rightarrow>nat\<Rightarrow>nat"
where
  tail_len_c_aux01:"tail_len_c_aux [] a = a"|
  tail_len_c_aux02:"tail_len_c_aux (h#T) a = tail_len_c_aux T (Suc(a))"

(* Definindo a funcao recursiva na cauda *)
fun tail_len_c::"'a list\<Rightarrow>nat"
where
  tail_len_c01:"tail_len_c [] = 0"|
  tail_len_c02:"tail_len_c T = tail_len_c_aux T 0"

(* ------------------------------------------- *)

(* Definindo a funcao recursiva normal *)
primrec tail_len_nc::"'a list\<Rightarrow>nat"
where
  tail_len_nc01:"tail_len_nc [] = 0"|
  tail_len_nc02:"tail_len_nc (h#T) = 1 + tail_len_nc T"

(* ------------------------------------------- *)

(* Provando teorema para nao recursivo na cauda = funcao 'length'*)
theorem th01:"tail_len_nc l = length l"
proof(induct l)
	show"tail_len_nc [] = length []"
	proof -
	have"tail_len_nc [] = 0" by(simp only:tail_len_nc01)
	also have" ... = length[]" by(simp)
	finally show"tail_len_nc [] = length []" by(simp)
qed
next
fix l0::"'a list" and e::'a
assume rec_nao_cald_hi: "tail_len_nc l0 = length l0"
	show"tail_len_nc (e#l0) = length (e#l0)"
	proof -
	have"tail_len_nc (e#l0) = tail_len_nc l0 + 1" by(simp only:tail_len_nc02)
	also have"... = length l0 + 1" by(simp only:rec_nao_cald_hi)
	also have"... = length (e#l0)" by(simp)
	finally show"tail_len_nc (e#l0) = length (e#l0)" by(simp)
qed
qed

(* Provando teorema para funcao recursiva na cauda = funcao 'length' *)
theorem th02:"\<forall>a. tail_len_c_aux l a = length l + a"
proof(induction l)
	show"\<forall>a. tail_len_c_aux [] a = length [] + a"
	proof(rule allI)
	fix a0::nat
	have "tail_len_c_aux [] a0 = a0" by(simp only:tail_len_c_aux01)
	also have"... = length [] + a0" by(simp)
	finally show"tail_len_c_aux [] a0 = length [] + a0" by(simp)
qed
next
fix l0::"'a list" and elem::'a
assume rec_cald_inv_hi:"\<forall>a. tail_len_c_aux l0 a = length l0 + a"
	show"\<forall>a. tail_len_c_aux (elem#l0) a = length (elem#l0) + a"
	proof (rule allI)
	fix a0::nat
	have"tail_len_c_aux (elem#l0) a0 = tail_len_c_aux l0 (Suc a0)" by(simp only:tail_len_c_aux02)
	also have"... = length l0 + (Suc a0)" by(simp only:rec_cald_inv_hi)
	also have"... = length (elem#l0) + a0" by(simp)
	finally show"tail_len_c_aux (elem#l0) a0 = length (elem#l0) + a0" by(simp)
qed
qed

(* Provando que a funcao recursiva na cauda eh igual a nao recursiva na cauda *)
theorem tail_len_equi: "tail_len_nc T = tail_len_c T"
proof(induct T)

(* Provando para o caso base *)
  have "tail_len_nc [] = 0" by (simp only:tail_len_nc01)
  also have "... = tail_len_c []" by (simp only:tail_len_c01)
  finally show "tail_len_nc [] = tail_len_c []" by simp

(* Provando para n+1 *)
next
fix T0::"'a list" and a0::'a
assume"tail_len_nc T0 = tail_len_c T0"
	show"tail_len_nc (a0#T0) = tail_len_c (a0#T0)"
	proof -
	have "tail_len_nc (a0#T0) = length (a0#T0)" by (simp only:th01)
	also have "... = tail_len_c_aux (a0#T0) 0" by (simp only:th02)
	also have "... = tail_len_c (a0#T0)" by (simp only: tail_len_c02)
	finally show "tail_len_nc (a0#T0) = tail_len_c (a0#T0)" by (simp)
qed
qed

end
