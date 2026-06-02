theory problema_2
  imports Main
begin

(*
  ============================================================
  DEFINIÇÃO DA FUNÇÃO tamanho
  ============================================================

  A função tamanho recebe uma lista
  e retorna a quantidade de elementos dela.

  Tipo:
    'a list \<Rightarrow> nat

  Significa:
    recebe uma lista de qualquer tipo ('a)
    e retorna um número natural (nat).
*)

fun tamanho :: "'a list \<Rightarrow> nat" where

  (*
    ========================================================
    CASO BASE
    ========================================================

    A lista vazia possui tamanho 0.
  *)
  "tamanho [] = 0"

| (*
     =======================================================
     CASO RECURSIVO
     =======================================================

     h = cabeça da lista
     t = cauda da lista

     Uma lista h#t possui:
       1 elemento (a cabeça)
       +
       o tamanho do restante da lista.

     Exemplo:

       tamanho [1,2,3]
       =
       1 + tamanho [2,3]
       =
       1 + (1 + tamanho [3])
       =
       1 + (1 + (1 + tamanho []))
       =
       1 + (1 + (1 + 0))
       =
       3
   *)
  "tamanho (h#t) = 1 + tamanho t"


(*
  ============================================================
  TESTES
  ============================================================

  Os comandos value executam a função
  e mostram o resultado calculado pelo Isabelle.
*)

(*
  ------------------------------------------------------------
  TESTE 1
  ------------------------------------------------------------

  Tamanho da lista vazia.
*)

value "tamanho ([]::nat list)"

(*
  Resultado esperado:
    0
*)


(*
  ------------------------------------------------------------
  TESTE 2
  ------------------------------------------------------------

  Lista com apenas um elemento.
*)

value "tamanho ([10]::nat list)"

(*
  Resultado esperado:
    1
*)


(*
  ------------------------------------------------------------
  TESTE 3
  ------------------------------------------------------------

  Lista com vários elementos.
*)

value "tamanho ([1,2,3,4,5]::nat list)"

(*
  Resultado esperado:
    5
*)


(*
  ------------------------------------------------------------
  TESTE 4
  ------------------------------------------------------------

  Lista de strings.

  Isso demonstra que a função é genérica
  e funciona para qualquer tipo.
*)

value "tamanho ([''a'', ''b'', ''c'']::string list)"

(*
  Resultado esperado:
    3
*)


(*
  ------------------------------------------------------------
  TESTE 5
  ------------------------------------------------------------

  Lista booleana.
*)

value "tamanho ([True, False, True]::bool list)"

(*
  Resultado esperado:
    3
*)


(*
  ============================================================
  EXPLICAÇÃO DA EXECUÇÃO RECURSIVA
  ============================================================

  Exemplo:

    tamanho [1,2,3]

  O Isabelle calcula assim:

    tamanho [1,2,3]
    =
    1 + tamanho [2,3]

    =
    1 + (1 + tamanho [3])

    =
    1 + (1 + (1 + tamanho []))

    =
    1 + (1 + (1 + 0))

    =
    3

  Isso mostra a recursão estrutural sobre listas.
*)


(*
  ============================================================
  PROPRIEDADE SIMPLES
  ============================================================

  Vamos provar que:
    toda lista possui tamanho maior ou igual a 0.

  Isso é simples porque nat nunca é negativo,
  mas serve como exemplo de prova formal.
*)

theorem tamanho_nao_negativo :
  "tamanho l >= 0"

proof (induction l)

  (*
    ----------------------------------------------------------
    CASO BASE
    ----------------------------------------------------------
  *)

  case Nil

  show ?case
    by simp

next

  (*
    ----------------------------------------------------------
    PASSO INDUTIVO
    ----------------------------------------------------------
  *)

  case (Cons h t)

  show ?case
    by simp

qed


(*
  ============================================================
  TESTE DA PROPRIEDADE
  ============================================================

  Isabelle já garantiu formalmente a propriedade
  através do teorema acima.
*)

end