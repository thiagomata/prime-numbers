# Fronteiras de Sobrevivência em Processos Companheiros Balanceados de Lacunas 2

**Autor:** Thiago Henrique Ramos da Mata
Pesquisador Independente<br>
**Email:** [thiago.henrique.mata@gmail.com](mailto:thiago.henrique.mata@gmail.com)  
**ORCID:** [0009-0002-7366-939X](https://orcid.org/0009-0002-7366-939X)  
**GitHub:** [@thiagomata](https://github.com/thiagomata)  
**License:** [CC BY 4.0](../LICENSE)<br>
**DOI:** [10.5281/zenodo.22955798](https://doi.org/10.5281/zenodo.22955798)

**Status da prova:** As identidades dos processos companheiros são provadas
exatamente; os teoremas assintóticos são condicionais às premissas declaradas
com cada resultado (ver [§1.1](#11-scope-and-evidence)). A verificação em
Stainless está pendente. Nenhum resultado é reivindicado para a peneira real.

## Resumo

<div align="justify">
<p style="text-align: justify">

Este artigo examina processos companheiros que reproduzem o crescimento global
exato das lacunas 2, mas mudam onde cada filtro as remove. Todo pai produz $r$
cópias e exatamente duas são removidas, como na sequência de peneira. O
companheiro pode colocar essas duas remoções aleatoriamente, proteger um alvo
escolhido, ou direcioná-las para ele. Essa construção separa o número de
lacunas 2 sobreviventes de sua localização perto da cabeça.

A fração local de destruição $f_r$ de um filtro é comparada com a taxa aleatória
$2/r$ por meio de $w_r=rf_r/2$. Sob a premissa declarada de posicionamento cego,
o produto cumulativo prova que todo valor finito fixo de $w_r$ preserva lacunas
2 em janelas quadradas; com as condições adicionais de disponibilidade e mistura,
ele produz lacunas 2 na cabeça infinitas vezes. A primeira fronteira ocorre
quando $w_r=1+c\log r$: janelas quadradas sobrevivem para $c < 1$, enquanto a
recorrência na cabeça sobrevive para $c < 1/2$. Sob as mesmas premissas
espaciais, um modelo separado de localização aleatória com quota exata dá as
mesmas fronteiras locais quando suas quotas normalizadas satisfazem a soma
cumulativa na taxa CRT e as condições de erro somável de população finita
derivadas abaixo. Ele preserva uma contagem de ataques aceitos, em vez da
recorrência balanceada por pai; manter apenas uma contagem de ataques CRT é
insuficiente. Nenhuma das premissas espaciais, de disponibilidade ou de mistura
usadas por esses teoremas condicionais é provada para a peneira real. Portanto,
provar que a peneira real permanece abaixo da fronteira da cabeça, junto com
disponibilidade persistente e o limite determinístico de discrepância declarado
em [§10](#10-conclusion), estabeleceria a conjectura dos primos gêmeos.
</p>
</div>

<a id="1-introduction"></a>

## 1. Introdução

Comece com os inteiros positivos e remova os múltiplos de números primos, um
primo por vez. Em um estágio encabeçado pelo primo $p$, os valores aceitos são
precisamente os inteiros não divisíveis por nenhum primo menor que $p$. Esses
sobreviventes se repetem periodicamente. Se $e_i$ e $e_{i+1}$ são sobreviventes
consecutivos, então $e_{i+1}-e_i$ é sua lacuna; as lacunas ao longo de um
período completo formam um ciclo finito.

Esse objeto periódico de valores aceitos é a **Sequência de Peneira**,
introduzida e formalmente verificada em [Formal Verification of Sieve Sequence Stages and Their
Transitions](https://doi.org/10.5281/zenodo.22955782) [[1]](#ref1); seu ciclo finito de lacunas é a
representação usada ao longo deste artigo.

Depois que os múltiplos de $2$ foram removidos, todo sobrevivente é ímpar. Toda
lacuna é, portanto, par, e $2$ é a menor lacuna possível. Uma **lacuna 2** é um
par de sobreviventes consecutivos $x$ e $x+2$. No estágio encabeçado por um
primo $Q$, todos os primos abaixo de $Q$ foram instalados como filtros. Uma
lacuna 2 sobrevivente cujos extremos estejam na janela segura pelo quadrado
$[Q,Q^2)$ é, portanto, um par de primos gêmeos: qualquer número composto abaixo
de $Q^2$ tem um divisor primo abaixo de $Q$ e já teria sido removido.

Quando a peneira mais tarde alcança o estágio encabeçado por $x$, o mesmo par
aparece como a primeira lacuna após a cabeça. Infinitas lacunas 2 desse tipo na
cabeça dariam infinitos pares de primos gêmeos. Mas a sobrevivência pode ser
perguntada em três escalas espaciais diferentes:

1. alguma lacuna 2 existe em algum lugar do período completo em toda camada;
2. uma lacuna 2 ocorre em cada janela segura pelo quadrado suficientemente grande; ou
3. a primeira lacuna após a cabeça distinguida é igual a $2$ infinitas vezes.

A primeira afirmação é global e puramente combinatória. A segunda é local, mas
se beneficia de uma janela cujo comprimento cresce quadraticamente. A terceira
diz respeito a uma posição e, portanto, não tem reserva de tamanho de janela.
Misturar esses significados esconde o limiar real.

As duas visões empíricas a seguir tornam a distinção visível na Sequência de
Peneira determinística. Elas usam os mesmos 200 estágios e a mesma compressão
focada em 2: toda lacuna 2 recebe sua própria célula verde, enquanto cada
sequência maximal de lacunas consecutivas que não são 2 é colapsada em uma
célula colorida igual à sua soma. Uma célula colorida interna, portanto, mede a
distância total entre duas lacunas 2 consecutivas. Ambas as visões exibem
$1{,}400$ unidades comprimidas de cada linha; elas diferem apenas em onde essas
linhas são posicionadas horizontalmente.

**Visão A — instantâneos comprimidos independentes.** Toda linha começa na
coluna zero, então sua coordenada horizontal conta unidades comprimidas a partir
da própria cabeça daquele estágio. Esta é a visão original. Ela mostra
honestamente a textura dentro de cada estágio, mas sua deriva vertical curva ou
ruidosa não deve ser lida como uma lacuna 2 mudando antes da fronteira
quadrada: colunas iguais em linhas adjacentes não precisam representar os mesmos
valores sobreviventes.

![Instantâneos independentes focados em 2 de 200 estágios da Sequência de Peneira: toda linha recomeça em sua própria cabeça](https://raw.githubusercontent.com/thiagomata/prime-numbers/master/charts/gap-heatmap-2focused.svg)

**Visão B — alinhamento seguro-2 compartilhado.** Para cada par de linhas
adjacentes, seja $h$ a cabeça do estágio anterior. Uma âncora segura é uma
lacuna 2 com o mesmo valor inicial bruto em ambas as linhas e com ambos os
extremos estritamente abaixo de $h^2$. O cálculo de alinhamento compara os
índices comprimidos de toda lacuna 2 segura compartilhada desse tipo e desloca a
linha posterior pela diferença comum delas. Ao longo das 199 transições
observadas, o conjunto de dados de 200 estágios exibe 118 diferenças de zero e
81 de um; toda âncora segura dentro de cada transição concorda com a diferença
daquela linha. Acumular essas diferenças produz a visão alternativa abaixo.

![Compressão alinhada por seguro-2 compartilhado de 200 estágios da Sequência de Peneira: lacunas 2 pré-quadrado inalteradas formam linhas verdes verticais](https://raw.githubusercontent.com/thiagomata/prime-numbers/master/charts/gap-heatmap-2focused-aligned.svg)

A cunha branca à esquerda é preenchimento intencional criado pelos deslocamentos
cumulativos. Um deslocamento zero ocorre quando avançar a cabeça apenas encurta a
execução inicial colapsada de lacunas não 2; um deslocamento de uma célula
ocorre quando esse passo remove uma execução comprimida inteira ou uma célula de
lacuna 2 isolada. Assim, as linhas verdes retas na Visão B e a textura curva na
Visão A descrevem os mesmos dados sob coordenadas diferentes.

A peneira não rotaciona essa linha comprimida como uma lista atômica. Dentro do
prefixo seguro, ela avança a cabeça por uma lacuna bruta; só depois a
visualização colapsa as lacunas consecutivas restantes que não são 2. Assim, um
prefixo bruto $[4,6,8,2,\ldots]$ aparece em linhas sucessivas como
$[18,2,\ldots] \to [14,2,\ldots] \to [8,2,\ldots] \to [2,\ldots]$. O longo
elemento azul não é uma lacuna mesclada inalterada reutilizada em várias
sequências; é o sufixo decrescente de uma execução bruta. Rotacionar uma célula
comprimida por linha mostraria esse bloco apenas uma vez, mas definiria uma
dinâmica diferente da Sequência de Peneira.

| Visão | Coordenada horizontal | O que a comparação vertical sustenta |
|---|---|---|
| Instantâneos independentes | Unidades comprimidas a partir da própria cabeça de cada linha | Densidade e textura de espaçamento dentro do estágio; não linhagem célula a célula |
| Alinhado por seguro-2 compartilhado | Colunas cumulativas fixadas por lacunas 2 compartilhadas abaixo do $h^2$ anterior | Alinhamento exato do prefixo seguro observado; não linhagem completa além dele |

Essas figuras fornecem contexto empírico para o problema de posicionamento;
nenhuma delas é evidência para os limiares de sobrevivência dos modelos
companheiros derivados abaixo. Elas são geradas pelo [cálculo do mapa de calor de lacunas](https://github.com/thiagomata/prime-numbers/blob/master/python/src/sieve_sequence/gap_heatmap.py) a partir de um conjunto de dados contendo as
[primeiras 100.000 lacunas de cada estágio](https://github.com/thiagomata/prime-numbers/blob/master/data/sieve-sequence/first_gaps_per_seq.csv).

A pergunta central, portanto, não é qual porcentagem fixa de comportamento pode
ser chamada de adversarial. É quão grande pode ser a destruição local realizada
em relação ao benchmark aleatório $2/r$, e como esse dano é alocado perto da
cabeça.

Os companheiros balanceados são projetados para separar essas questões. Eles
retêm o número exato de descendentes da peneira real, mas substituem a regra
aritmética que seleciona quais descendentes morrem. Isso torna a sobrevivência
global idêntica em todo companheiro, enquanto permite que o comportamento local
varie de maximamente protetor, passando por aleatório cego à posição, até
maximamente hostil.

Estabelecemos:

- a recorrência global exata independente de alocação $N_{k+1}=(r_k-2)N_k$;
- a lei cumulativa de risco local $P(Q)=e^{-D(Q)}$ e suas fronteiras de
  sobrevivência de fator fixo e logarítmicas;
- os limiares distintos de janela quadrada e cabeça para misturas
  adversarial/aleatória e adversarial/protetora;
- limites finitos agudos de alocação separando orçamento de rótulo adversarial
  de informação posicional; e
- companheiros de quota exata e quota exata enviesada que preservam contagens
  de ataques CRT enquanto aleatorizam suas localizações.

<a id="11-scope-and-evidence"></a>

### 1.1 Escopo e Evidência

Provamos identidades exatas para os processos companheiros finitos e teoremas
condicionais para seu comportamento local assintótico. Sempre que um resultado
precisa de uniformidade espacial, disponibilidade na cabeça ou mistura entre
camadas, declaramos essa premissa na própria propriedade antes de usá-la. A
comparação com a peneira real mostra então qual informação aritmética adicional
transferiria o resultado companheiro.

Os teoremas companheiros abaixo são provados matematicamente sob suas premissas
declaradas; a verificação em Stainless permanece pendente e está fora do escopo
deste artigo.

<a id="2-preliminaries-and-companion-models"></a>

## 2. Preliminares e Modelos Companheiros

Seja $\mathcal G_k$ o conjunto de descendentes de lacunas 2 antes de instalar o
primo $r$. Cada pai $g\in\mathcal G_k$ produz as cópias indexadas

```math
(g,0),(g,1),\ldots,(g,r-1).
```

Exatamente dois índices distintos são prejudiciais. Cada pai recebe uma de três
políticas. Um **pai aleatório** sorteia o par prejudicial uniformemente dos
subconjuntos de dois elementos de $\mathbb Z/r\mathbb Z$. Um **pai
adversarial** coloca uma deleção em seu filho-alvo sempre que possível. Um **pai
protetor**, definido completamente em [§5.2](#52-the-protective-parent-policy),
coloca ambas as deleções longe do alvo sempre que possível.

Toda política deixa exatamente $r-2$ filhos. Os companheiros, portanto, mudam a
localização das deleções, não o tamanho da população.

Por exemplo, seja $r=5$ e suponha que o índice de filho $1$ seja o alvo. Um pai
aleatório pode remover qualquer par, como $\{0,4\}$. Um pai adversarial escolhe
um par contendo $1$, como $\{1,4\}$. Um pai protetor escolhe ambos os índices
fora do alvo, novamente permitindo $\{0,4\}$. Os três pais fazem escolhas locais
diferentes, mas cada um deixa exatamente três filhos. Esse exemplo simples é a
distinção usada ao longo do artigo: a reprodução global é fixa, enquanto o
posicionamento local muda.

As definições de companheiro aleatório, adversarial e protetor acima são as
definições usadas ao longo deste artigo. O par modular real correspondente é
derivado em [Dinâmica de Lacunas §6.1](https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter6/gap-dynamics.md#61-one-new-prime-forbids-two-copy-classes) [[2]](#ref2).

O processo de quota exata introduzido em [§7](#7-exact-quota-companion-processes)
é um experimento separado de localização aleatória condicional. Ele sorteia um
número fixo de ataques de uma população elegível e pode atacar zero, um ou dois
descendentes de um dado pai de lacuna 2. Portanto, ele não satisfaz a
recorrência balanceada por pai $r-2$; seu papel é comparar a sobrevivência local
condicional sob uma quota fixa de ataques.

<a id="21-notation"></a>

### 2.1 Notação

Usamos a seguinte notação ao longo do texto:

| Símbolo | Significado |
|---|---|
| $r$ | primo de filtro entrante |
| $Q$ | cabeça prima alvo |
| $N_k$ | população de lacunas 2 em período completo na camada $k$ |
| $f_r$ | probabilidade condicional de destruição de uma linhagem elegível rastreada |
| $\widehat f_r$ | fração de destruição observada em uma população finita especificada |
| $w_r=rf_r/2$ | destruição relativa ao benchmark aleatório $2/r$ |
| $D(Q)=\sum_{r < Q}-\log(1-f_r)$ | risco local cumulativo |
| $\alpha_r$ | parcela adversarial absoluta programada em uma mistura |
| $A(Q)=\sum_{r < Q}-\log(1-\alpha_r)$ | risco cumulativo da parcela adversarial |
| $J_r/N_r=u_r$ | fração de ataques de quota exata |
| $\beta_r$ | preferência bruta por extremos em uma quota enviesada |
| $\kappa_r$ | viés efetivo de destruição, igual a $w_r$ quando medido a partir de $f_r$ |

Salvo quando um intervalo diferente é exibido, produtos e somas de filtros
percorrem primos $r_0\le r < Q$, com $r_0\ge5$ fixo. Todo prefixo finito tem
fatores de sobrevivência estritamente positivos. Programações de cauda são
impostas apenas depois que seus riscos estão em $[0,1)$. Um prefixo letal não
pode ser absorvido em uma constante positiva.

Para afirmações probabilísticas, todos os eventos candidatos são definidos em
um único espaço de probabilidade. Para cada candidato, $f_r$ é sua probabilidade
condicional determinística de destruição, dada a elegibilidade inicial e a
sobrevivência pelos filtros anteriores. O modelo de risco comum assume que essas
probabilidades são as mesmas para os candidatos comparados. A regra da cadeia
então dá uma probabilidade de sobrevivência candidata $P(Q)$; a independência
entre candidatos é uma questão separada.

Aplicações em janelas assumem $B(Q)\asymp Q^2$ histórias candidatas elegíveis,
cada uma com probabilidade de sobrevivência $P(Q)$. Aplicações na cabeça
assumem uma probabilidade de elegibilidade $b_Q$ limitada inferiormente por uma
constante positiva e a mesma lei de sobrevivência condicional à elegibilidade.
Consequentemente,

```math
\begin{aligned}
\lambda_Q:=\mathbb E[X_Q]&=B(Q)P(Q)
&&[\text{Linearidade da Esperança}],\\
\Pr(H_Q)&=b_QP(Q)
&&[\text{Probabilidade Condicional}].
\end{aligned}
```

Essas hipóteses marginais são adicionais à regra balanceada de ramificação. Elas
não são fornecidas por sua contagem global. Experimentos diferentes de janela e
cabeça não precisam descrever uma única sequência aleatória aninhada de
inteiros.

Para os eventos de cabeça $H_Q$ indexados por primos, defina

```math
S(X):=
\sum_{\substack{Q\le X\\Q\text{ prime}}}\Pr(H_Q).
```

Ao longo deste artigo, **mistura adequada entre camadas** significa que, sempre
que $S(X)\longrightarrow\infty$,

```math
\sum_{\substack{P,Q\le X\\P,Q\text{ prime}}}
\Pr(H_P\cap H_Q)
=
(1+o(1))S(X)^2.
```

A independência mútua é um caso especial suficiente: sua correção diagonal é
$O(S(X))=o(S(X)^2)$. A forma de Kochen--Stone do segundo lema de
Borel--Cantelli então dá $\Pr(H_Q\text{ infinitas vezes})=1$ [[3]](#ref3).
Quando $S(X)$ converge, o primeiro lema de Borel--Cantelli dá apenas finitos
eventos de cabeça sem qualquer premissa de mistura.

Aplicações em janelas quadradas usam uma premissa nomeada adicional.
**Posicionamento cego** significa que os inícios sobreviventes são colocados na
janela de modo que o limite de janela vazia

```math
\Pr(X_Q=0)\le e^{-\lambda_Q}
```

vale, onde $\lambda_Q$ é a população sobrevivente esperada dessa janela (por
exemplo $\lambda_Q^{\mathrm{mix}}$ em [§4.1](#41-adversarialrandom-parent-square-window-boundary)). Esta é uma hipótese sobre
a distribuição conjunta de posicionamento: ela vale para posicionamento
uniforme independente e não é derivada neste artigo para alocadores dependentes,
como quotas exatas, moedas de filtro inteiro ou balanço por blocos. Sempre que
um resultado de janela quadrada a usa, o resultado diz isso; aplica-se a mesma
ressalva de [§9](#9-limitations) — alocadores com estruturas de dependência
diferentes não podem herdar entre si conclusões quase certas.

<a id="22-mathematical-foundation"></a>

### 2.2 Fundação Matemática

A construção companheira usa três resultados exatos da sequência de peneira
provados em [Dinâmica de Lacunas](https://doi.org/10.5281/zenodo.22955786) [[2]](#ref2):

- a [contagem exata de lacunas 2 em período completo](https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter6/gap-dynamics.md#52-exact-non-recursive-global-count);
- as [duas classes prejudiciais de índices de cópia](https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter6/gap-dynamics.md#61-one-new-prime-forbids-two-copy-classes); e
- a [contagem exata de ataques aceitos](https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter6/gap-dynamics.md#91-exact-accepted-strikes).

A normalização de dano local relativo é definida diretamente em [§3.2](#32-local-destruction-relative-to-random), e seu
refinamento por alocação é definido em [§6.2](#62-targeting-and-local-hazard).

<a id="3-relative-hazard-and-survival-frontiers"></a>

## 3. Risco Relativo e Fronteiras de Sobrevivência

<a id="31-global-persistence-is-independent-of-allocation"></a>

### 3.1 A Persistência Global é Independente da Alocação

Começamos com a propriedade compartilhada por todo companheiro balanceado.
Nenhuma escolha do par prejudicial muda o número de descendentes sobreviventes:
pais aleatórios, adversariais, protetores e mistos deixam todos a mesma
população global. A extinção local deve, portanto, vir do posicionamento, não do
esgotamento do suprimento de período completo.

Seja $N_k=|\mathcal G_k|$ e suponha $N_0>0$. Instalar $r_k$ dá

```math
\begin{aligned}
N_{k+1}
&=\sum_{g\in\mathcal G_k}(r_k-2)
&&[\text{Exatamente Duas Cópias Removidas por Pai}]\\
&=(r_k-2)N_k.
&&[\text{Simplificação}]
\end{aligned}
```

Consequentemente,

```math
\begin{aligned}
N_k
&=N_0\prod_{i < k}(r_i-2)
&&[\text{Iteração}]\\
& > 0
&&[N_0>0;\ r_i\ge5]\\
&\longrightarrow\infty.
&&[\text{Todo Fator é Pelo Menos }3]
\end{aligned}
```

Assim

```math
\text{a persistência global de lacunas 2 vale para toda programação adversarial.}
\qquad[\text{C.Q.D.}]
```

O registro completo da prova aparece no [Apêndice A.1](#appendix-a1). A
contagem correspondente da peneira real é provada em [Dinâmica de Lacunas §5.2](https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter6/gap-dynamics.md#52-exact-non-recursive-global-count) [[2]](#ref2).

<a id="32-local-destruction-relative-to-random"></a>

### 3.2 Destruição Local Relativa ao Aleatório

Duas quantidades precisam ser distinguidas. Se $L_r > 0$ lacunas estão presentes
em uma população finita especificada e $H_r$ são destruídas, sua fração observada é

```math
\widehat f_r:=\frac{H_r}{L_r},
\qquad \widehat w_r:=\frac{r\widehat f_r}{2}.
```

O modelo probabilístico, em vez disso, usa o risco condicional de linhagem
$f_r$ definido em [§2.1](#21-notation). A seleção aleatória balanceada tem taxa
condicional de destruição

```math
d_r:=\frac2r.
```

O fator adimensional pior-que-aleatório é

```math
w_r
:=\frac{f_r}{d_r}
=\frac{rf_r}{2}.
```

Esta é a escala significativa de adversarialidade porque o próprio benchmark
encolhe à medida que os filtros crescem:

```math
\begin{aligned}
w_r=0
&\Longleftrightarrow f_r=0
&&[\text{Extremo Protetor}],\\
w_r=1
&\Longleftrightarrow f_r=2/r
&&[\text{Benchmark Aleatório}],\\
w_r=r/2
&\Longleftrightarrow f_r=1
&&[\text{Destruição Local Completa}].
\end{aligned}
```

O intervalo $0\le w_r\le r/2$ compara dano condicional com a lei neutra. O
escore observado análogo $\widehat w_r$ pode flutuar acima de um mesmo para um
filtro aleatório. Uma fração observada não estabelece por si só a probabilidade
condicional de destruição de um filho particular.

#### Parcela Adversarial/Aleatória Absoluta como Especialização

Fixe um alvo: uma janela segura pelo quadrado ou uma posição distinguida na
cabeça. No filtro $r$, seja

```math
0\le \alpha_r\le 1
```

a parcela adversarial. A parcela restante $1-\alpha_r$ usa a escolha aleatória
balanceada.

Isso pode ser interpretado pai por pai ou como uma mistura marginal para uma
linhagem localmente relevante. Para o produto cumulativo estudado abaixo, as
escolhas de mistura para uma linhagem rastreada são independentes de um filtro
para o próximo. O cálculo de uma linhagem em cada filtro é então o mesmo:

- sob seleção adversarial, seu filho-alvo é destruído;
- sob seleção aleatória balanceada, esse filho sobrevive com probabilidade
  $1-2/r$.

O modelo, portanto, assume que o ramo adversarial é forte o bastante para
identificar e matar o filho localmente relevante. É exatamente isso que o torna
uma comparação adversarial, em vez de uma descrição do filtro real.

Sua taxa total de destruição local e seu fator relativo são

```math
\begin{aligned}
f_r
&=\alpha_r+(1-\alpha_r)\frac2r,\\
w_r
&=\frac r2f_r\\
&=1+\frac{r-2}{2}\alpha_r.
\end{aligned}
```

Assim, uma parcela absoluta fixa $\alpha_r=\alpha > 0$ não representa uma
quantidade fixa pior que a aleatória. Ela faz $w_r$ crescer linearmente como
$\alpha r/2$. É por isso que o modelo de parcela fixa é assintoticamente fatal
por uma razão essencialmente trivial; a pergunta não trivial é quão rapidamente
o próprio $w_r$ pode crescer.

<a id="33-the-general-cumulative-local-hazard-law"></a>

### 3.3 A Lei Geral de Risco Local Cumulativo

Acompanhe um candidato elegível através de filtros sucessivos. Pela definição
de risco condicional, sua próxima probabilidade de sobrevivência é

```math
s_r=1-f_r=1-\frac{2w_r}{r}.
```

Assuma $f_r < 1$ para todo filtro na cadeia rastreada. Defina o risco local
cumulativo

```math
D(Q)
:=\sum_{r < Q}-\log(1-f_r)
=\sum_{r < Q}-\log\left(1-\frac{2w_r}{r}\right).
```

O fator completo de sobrevivência é exatamente

```math
\begin{aligned}
P(Q)
&=\prod_{r < Q}(1-f_r)
&&[\text{Regra da Cadeia de Probabilidade Condicional}]\\
&=\exp\left(\sum_{r < Q}\log(1-f_r)\right)
&&[\text{Produto para Soma}]\\
&=e^{-D(Q)}.
&&[\text{Definição de }D(Q)]
\end{aligned}
\qquad[\text{C.Q.D.}]
```

Há também uma versão determinística. Para uma coorte aninhada fixa sem
nascimentos ou imigração, $L_{r^+}=L_r(1-\widehat f_r)$ telescopa para a razão
entre o tamanho final e inicial da coorte. Esta é uma razão observada, não uma
probabilidade marginal. Mudar a janela alvo ou introduzir novos descendentes
quebra esse telescópio, a menos que uma identidade contábil adicional seja
provada.

O Teorema dos Números Primos, a estimativa harmônica dos primos e suas
consequências por soma parcial usadas aqui e abaixo são clássicos; usamos Hardy
e Wright [[4]](#ref4).

Para o benchmark aleatório $w_r=1$,

```math
\begin{aligned}
D_{\mathrm{random}}(Q)
&=\sum_{r < Q}-\log\left(1-\frac2r\right)\\
&=2\log\log Q+O(1),
\end{aligned}
```

e portanto

```math
P_{\mathrm{random}}(Q)
\asymp\frac{C}{(\log Q)^2}.
```

A mistura adversarial/aleatória absoluta de [§3.2](#32-local-destruction-relative-to-random) é recuperada porque

```math
1-f_r
=(1-\alpha_r)\left(1-\frac2r\right).
```

Se

```math
A(Q):=\sum_{r < Q}-\log(1-\alpha_r),
```

então

```math
\begin{aligned}
D_{\mathrm{adversarial/random}}(Q)
&=D_{\mathrm{random}}(Q)+A(Q),\\
P_{\mathrm{adversarial/random}}(Q)
&\asymp\frac{C}{(\log Q)^2}e^{-A(Q)}.
\end{aligned}
```

Assim, o $A(Q)$ anterior é um risco excedente criado por uma mistura particular
de políticas. A quantidade primária é $D(Q)$, que também se aplica quando não
existe rótulo de política $\alpha_r$.

Se um filtro tem $f_r=1$, a extinção local é imediata e o risco cumulativo é
infinito a partir desse ponto.

O registro completo da prova aparece no [Apêndice A.2](#appendix-a2).

<a id="34-every-fixed-finite-worsening-factor-survives"></a>

### 3.4 Todo Fator Fixo Finito de Piora Sobrevive

A taxa aleatória de destruição encolhe como $2/r$. Primeiro perguntamos o que
acontece quando o filtro local é um número fixo de vezes pior que esse
benchmark. Com um suprimento quadrático de inícios elegíveis e posicionamento
cego, todo fator fixo ainda deixa janelas quadradas ocupadas. Se candidatos na
cabeça permanecem disponíveis e camadas sucessivas se misturam adequadamente, a
cabeça também retorna a uma lacuna 2 infinitas vezes.

Seja $w\ge 0$ fixo e suponha

```math
f_r=\frac{2w}{r}
```

para todos os filtros suficientemente grandes. Um prefixo finito é absorvido em
uma constante positiva. Como os termos quadráticos de erro são somáveis sobre
primos,

```math
\begin{aligned}
D_w(Q)
&=\sum_{r < Q}-\log\left(1-\frac{2w}{r}\right)
&&[\text{Definição de }D(Q)]\\
&=2w\sum_{r < Q}\frac1r+O(1)
&&[\text{Expansão de Taylor; Resto Somável}]\\
&=2w\log\log Q+O(1).
&&[\text{Soma Harmônica dos Primos}]
\end{aligned}
```

Portanto

```math
P_w(Q)\asymp\frac{C_w}{(\log Q)^{2w}}.
```

Para uma janela quadrada com $B(Q)\asymp C_0Q^2$ linhagens elegíveis,

```math
\lambda_w(Q)
\asymp
C_0\frac{Q^2}{(\log Q)^{2w}}
\longrightarrow\infty
```

para todo $w$ finito. O crescimento é forte o suficiente para tornar somável o
limite padrão de janela vazia, então apenas finitas janelas quadradas são vazias
quase certamente sob a premissa de posicionamento cego.

Para uma cabeça distinguida com disponibilidade de base limitada inferiormente,

```math
\Pr(H_Q)\asymp\frac{C_w}{(\log Q)^{2w}}.
```

A soma dessa probabilidade sobre cabeças primas diverge para todo $w$ finito.
Sob mistura adequada, lacunas 2 na cabeça, portanto, recorrem infinitas vezes
quase certamente.

Assim

```math
\text{não há máximo finito de fator constante pior que o aleatório.}
\qquad[\text{C.Q.D.}]
```

Um filtro que é duas, dez ou um milhão de vezes pior que a taxa aleatória ainda
fica na mesma classe assintótica de sobrevivência uma vez que $r$ seja
suficientemente grande. A transição não trivial começa apenas quando $w_r$
cresce com $r$.

O registro completo da prova aparece no [Apêndice A.3](#appendix-a3).

A conclusão de fator fixo não é apenas assintótica; ela é visível na própria
ocupação da janela quadrada. A figura abaixo plota $\log_{10}\lambda_w(Q)$
contra $\log_{10}Q$ para os fatores fixos $w=1,3,6,10$, uma parcela
adversarial constante de $1\%$ e a fronteira $c=1$, $w_r=1+\log r$. Todo $w$
finito fixo sobe sem limite -- $w=6$ e $w=10$ caem visivelmente primeiro,
porque $Q^2$ precisa primeiro ultrapassar $(\log Q)^{2w}$ -- enquanto a parcela
constante colapsa rapidamente e a fronteira exata $c=1$ declina apenas
logaritmicamente: $\lambda_1(Q)\asymp C/(\log Q)^2\to0$. Esta é a fronteira do
lado de falha derivada em [§3.5](#35-logarithmically-growing-worsening-has-two-thresholds), não uma curva sobrevivente.

![Ocupação esperada de janela quadrada log10(lambda(Q)) em escala logarítmica: todo fator fixo de risco relativo w=1,3,6,10 eventualmente sobe sem limite, uma parcela adversarial constante de 1% colapsa rapidamente, e a fronteira exata c=1 declina lentamente até zero](https://raw.githubusercontent.com/thiagomata/prime-numbers/master/charts/phase-transition-window.svg)

<a id="35-logarithmically-growing-worsening-has-two-thresholds"></a>

### 3.5 Piora Logaritmicamente Crescente Tem Dois Limiares

A primeira transição genuína aparece quando o fator de piora cresce com o
filtro. Usando as mesmas premissas de suprimento, disponibilidade e mistura de
[§3.4](#34-every-fixed-finite-worsening-factor-survives), fazemos o fator
crescer logaritmicamente e comparamos a reserva fornecida por uma janela
quadrada com a reserva muito mais fina em uma cabeça distinguida.

```math
w_r=1+c\log r,
\qquad c\ge0.
```

A taxa total de destruição local é

```math
f_r
=\frac{2w_r}{r}
=\frac2r+2c\frac{\log r}{r}.
```

A contribuição aleatória fornece o primeiro termo, enquanto o segundo é o
excesso crescente. A soma sobre primos dá

```math
\begin{aligned}
D_c(Q)
&=\sum_{r < Q}-\log(1-f_r)
&&[\text{Definição de }D(Q)]\\
&=2\sum_{r < Q}\frac1r
&\quad+2c\sum_{r < Q}\frac{\log r}{r}+O(1)
&&[\text{Substituição; Resto Somável}]\\
&=2\log\log Q+2c\log Q+O(1).
&&[\text{Assintótica de Soma sobre Primos}]
\end{aligned}
```

Logo

```math
P_c(Q)
\asymp
\frac{C_c}{Q^{2c}(\log Q)^2}.
\qquad[\text{Exponenciação e Simplificação}]
```

Para um suprimento quadrático de janela quadrada,

```math
\lambda_c(Q)
\asymp
C_0\frac{Q^{2-2c}}{(\log Q)^2}.
```

Portanto

```math
\begin{aligned}
c < 1
&\Longrightarrow
\text{janelas quadradas eventualmente não vazias quase certamente},\\
c\ge1
&\Longrightarrow
\text{a esperança da janela quadrada tende a zero}.
\end{aligned}
```

Para a cabeça,

```math
\Pr(H_Q)
\asymp
\frac{C_c}{Q^{2c}(\log Q)^2}.
```

Somar sobre cabeças primas tem o mesmo comportamento de convergência que

```math
\int^\infty
\frac{dx}{x^{2c}(\log x)^3}.
```

Assim

```math
\begin{aligned}
c < \frac12
&\Longrightarrow
\text{infinitos eventos de cabeça quase certamente, com mistura},\\
c\ge\frac12
&\Longrightarrow
\text{apenas finitos eventos de cabeça quase certamente}.
\end{aligned}
```

O limiar é a regra de decisão de Borel-Cantelli para a cabeça, e a figura
abaixo o avalia diretamente. Ela plota a soma cumulativa de $\Pr(H_Q)$ sobre
primos reais enumerados até $Q$, para $w_r=1+c\log r$ em
$c=0.0,0.1,0.3,0.5,0.7,1.0$. Abaixo do limiar, a soma continua subindo --
$c=0.0$ e $c=0.1$ claramente, $c=0.3$ mais lentamente mas de modo provado --
então há infinitos eventos de cabeça com mistura. No limiar e acima dele, a
soma achata: $c=0.5$ apenas muito lentamente (é a própria fronteira), $c=0.7$ e
$c=1.0$ rapidamente -- então há apenas finitos eventos, quase certamente.

![Soma cumulativa de Pr(cabeça é uma lacuna 2) sobre primos enumerados, escala logarítmica: c=0.0 e c=0.1 sobem todo o caminho, c=0.3 sobe lentamente, c=0.5 achata apenas muito lentamente na fronteira, e c=0.7 e c=1.0 achatam rapidamente -- o limiar de Borel-Cantelli c=1/2](https://raw.githubusercontent.com/thiagomata/prime-numbers/master/charts/phase-transition-head.svg)

Equivalentemente, os regimes robustos de fator relativo são

```math
\begin{aligned}
w_r& < (1-\varepsilon)\log r
&&[\text{Sobrevivência em Janela Quadrada}],\\
w_r& < \left(\frac12-\varepsilon\right)\log r
&&[\text{Recorrência na Cabeça}],
\end{aligned}
```

até a base aleatória aditiva assintoticamente desprezível. Em termos da fração
total de destruição do segmento,

```math
\begin{aligned}
f_r& < (2-\varepsilon)\frac{\log r}{r}
&&[\text{Sobrevivência em Janela Quadrada}],\\
f_r& < (1-\varepsilon)\frac{\log r}{r}
&&[\text{Recorrência na Cabeça}].
\end{aligned}
\qquad[\text{C.Q.D.}]
```

Esses são regimes assintóticos cumulativos, não permissões pontuais que
reiniciam em cada filtro. Programações irregulares precisam ser avaliadas por
meio de $D(Q)$.

O registro completo da prova aparece no [Apêndice A.4](#appendix-a4).

<a id="36-relative-to-random-phase-diagram"></a>

### 3.6 Diagrama de Fases Relativo ao Aleatório

A resposta não é uma porcentagem fixa máxima. É uma fronteira de taxa de
crescimento para o dano local realizado relativo ao benchmark aleatório.

| Fator relativo realizado | Destruição local total | Janelas quadradas | Lacunas 2 na cabeça |
|---|---:|---|---|
| $w_r=1$ | $2/r$ | Eventualmente não vazias quase certamente | Infinitas vezes com mistura |
| Qualquer $w_r=w$ finito fixo | $2w/r$ | Eventualmente não vazias quase certamente | Infinitas vezes com mistura |
| $w_r=1+c\log r$, $0\le c < 1/2$ | $2/r+2c\log r/r$ | Eventualmente não vazias quase certamente | Infinitas vezes com mistura |
| $w_r=1+c\log r$, $1/2\le c < 1$ | $2/r+2c\log r/r$ | Eventualmente não vazias quase certamente | Apenas finitas vezes quase certamente |
| $w_r=1+c\log r$, $c\ge1$ | $2/r+2c\log r/r$ | População esperada tende a zero | Apenas finitas vezes quase certamente |
| $f_r=1$ em um passo rastreado | $1$ | Essa coorte rastreada é perdida | Esse candidato é perdido |

Consequentemente, **não há maior múltiplo constante finito do aleatório**. Para
sobrevivência em janela quadrada, o filtro pode se tornar quase $\log r$ vezes
pior que o aleatório; para lacunas 2 na cabeça recorrendo infinitamente, ele
pode se tornar quase $\tfrac12\log r$ vezes pior. Em termos de destruição local
total, os regimes suficientes robustos são, respectivamente,

```math
f_r < (2-\varepsilon)\frac{\log r}{r}
\qquad\text{e}\qquad
f_r < (1-\varepsilon)\frac{\log r}{r}.
```

Essas conclusões dizem respeito ao dano realizado dentro do segmento rastreado.
Um pequeno orçamento adversarial global ainda pode causar $f_r=1$ se for
alocado com informação de alvo suficiente; o teorema de alocação em [§5](#5-allocation-and-the-protective-parent) isola esse
segundo eixo.

<a id="4-absolute-share-mixtures"></a>

## 4. Misturas de Parcela Absoluta

<a id="41-adversarialrandom-parent-square-window-boundary"></a>

### 4.1 Fronteira de Janela Quadrada para Pais Adversariais/Aleatórios

Agora expressamos o resultado geral de risco por meio de uma mistura explícita.
Cada pai é adversarial com parcela $\alpha_r$ e, caso contrário, aleatório.
Quando os inícios sobreviventes seguem o modelo de uniformidade espacial do
companheiro aleatório balanceado, uma janela segura pelo quadrado tem comprimento

```math
L_Q\asymp Q^2.
```

A população mista esperada é

```math
\begin{aligned}
\lambda_Q^{\mathrm{mix}}
&=L_Q\delta_Q^{\mathrm{mix}}
&&[\text{Ocupação Uniforme Esperada}]\\
&\asymp
C\frac{Q^2}{(\log Q)^2}e^{-A(Q)}.
&&[\text{Substituição}]
\end{aligned}
```

Tomar logaritmos expõe o limiar:

```math
\begin{aligned}
\log\lambda_Q^{\mathrm{mix}}
&=2\log Q-2\log\log Q-A(Q)+O(1).
&&[\text{Logaritmo}]
\end{aligned}
```

Portanto, para todo $\varepsilon > 0$ fixo,

```math
\begin{aligned}
A(Q)\le(2-\varepsilon)\log Q
&\Longrightarrow
\lambda_Q^{\mathrm{mix}}\longrightarrow\infty,
&&[\text{Orçamento Adversarial Subcrítico}]\\
A(Q)\ge(2+\varepsilon)\log Q
&\Longrightarrow
\lambda_Q^{\mathrm{mix}}\longrightarrow0.
&&[\text{Orçamento Adversarial Supercrítico}]
\end{aligned}
```

A fronteira $A(Q)=2\log Q+o(\log Q)$ exige seus termos de ordem menor; a
contribuição $-2\log\log Q$ não pode ser descartada ali.

Sob posicionamento uniforme, uma estimativa de janela vazia tem a forma usual

```math
\Pr(X_Q=0)\le e^{-\lambda_Q^{\mathrm{mix}}}.
```

Sempre que

```math
\sum_{Q\text{ prime}}e^{-\lambda_Q^{\mathrm{mix}}} < \infty,
```

o primeiro lema de Borel-Cantelli dá apenas finitas janelas quadradas vazias
quase certamente. Uma condição suficiente conveniente é

```math
\lambda_Q^{\mathrm{mix}}\ge(1+\varepsilon)\log Q
\qquad[\text{C.Q.D.}]
```

para todo $Q$ suficientemente grande. Isso é mais forte do que meramente exigir
$\lambda_Q^{\mathrm{mix}}\to\infty$ e impede que uma esperança lentamente
divergente seja confundida com um teorema de sobrevivência eventual.

Isso prova ocupação eventual de janelas seguras dentro do companheiro misto
espacialmente uniforme. A Seção 8 declara as condições separadas necessárias
para transferir o resultado para a peneira real.

O registro completo da prova aparece no [Apêndice A.5](#appendix-a5).

<a id="42-why-a-constant-absolute-adversarial-share-is-locally-fatal"></a>

### 4.2 Por que uma Parcela Adversarial Absoluta Constante é Localmente Fatal

Uma parcela adversarial constante soa branda, mas adiciona a mesma perda
positiva em todo filtro enquanto o benchmark aleatório continua encolhendo.
Portanto, esperamos que ela sobrecarregue a sobrevivência local. Seja uma
parcela fixa $0 < \alpha < 1$ adversarial em todo filtro. Então

```math
\begin{aligned}
A(Q)
&=-\bigl(\pi(Q)+O(1)\bigr)\log(1-\alpha)
&&[\text{Parcela Constante}]\\
&\asymp
\bigl[-\log(1-\alpha)\bigr]\frac{Q}{\log Q}.
&&[\text{Teorema dos Números Primos}]
\end{aligned}
```

Como $Q/\log Q$ cresce mais rápido do que $\log Q$, isso fica muito acima do
orçamento crítico da janela quadrada. Logo

```math
\begin{aligned}
\lambda_Q^{(\alpha)}
&\asymp
C\frac{Q^2}{(\log Q)^2}(1-\alpha)^{\pi(Q)}\\
&\longrightarrow0.
&&[\text{Perda Exponencial Supera Crescimento Quadrático}]
\end{aligned}
```

Assim

```math
\text{toda parcela adversarial positiva fixa por filtro é localmente fatal}
\qquad[\text{C.Q.D.}]
```

no modelo de mistura repetida, embora a população de período completo continue a
crescer sem limite.

Isso é diferente de aplicar uma diluição adversarial depois que todos os filtros
aleatórios terminaram. Uma diluição única multiplica a contagem final por
$1-\alpha$ uma vez; o modelo repetido a multiplica uma vez por primo. Confundir
esses dois experimentos inverte a conclusão assintótica.

<a id="43-two-decaying-absolute-share-families"></a>

### 4.3 Duas Famílias de Parcela Absoluta Decrescente

A pergunta útil, portanto, não é “qual porcentagem fixa é tolerável?” A
pergunta útil é quão rapidamente $\alpha_r$ precisa decair. Nesta seção e na
comparação em [§5](#5-allocation-and-the-protective-parent), as programações
exibidas valem exatamente para todos os filtros suficientemente grandes. Mera
equivalência assintótica dá controle mais fraco do resto e não determina os
casos críticos.

#### Decaimento Recíproco: $\alpha_r= c/r$

Para $c > 0$ fixo e primos suficientemente grandes,

```math
\begin{aligned}
A(Q)
&=c\sum_{r < Q}\frac1r+O(1)
&&[\text{Expansão de Taylor; Erro Somável}]\\
&=c\log\log Q+O(1).
&&[\text{Soma Harmônica dos Primos}]
\end{aligned}
```

Portanto

```math
e^{-A(Q)}\asymp\frac1{(\log Q)^c}
```

e

```math
\lambda_Q^{\mathrm{mix}}
\asymp
C\frac{Q^2}{(\log Q)^{2+c}}\longrightarrow\infty.
```

A população da janela cresce polinomialmente mais rápido que suas perdas
logarítmicas, então as probabilidades de janela vazia são somáveis sob o modelo
espacial.

#### Decaimento Logarítmico-sobre-Linear: $\alpha_r= c\log r/r$

Para um prefixo inicial finito, defina as parcelas separadamente para que
permaneçam em $[0,1)$; isso muda apenas a constante final positiva. Na cauda
assintótica,

```math
\begin{aligned}
A(Q)
&=c\sum_{r < Q}\frac{\log r}{r}+O(1)
&&[\text{Expansão de Taylor; Erro Somável}]\\
&=c\log Q+O(1).
&&[\text{Teorema dos Números Primos por Soma Parcial}]
\end{aligned}
```

Consequentemente,

```math
\begin{aligned}
e^{-A(Q)}&\asymp Q^{-c},\\
\lambda_Q^{\mathrm{mix}}
&\asymp C\frac{Q^{2-c}}{(\log Q)^2}.
\end{aligned}
```

O diagrama de fases de janela quadrada é, portanto,

```math
\begin{aligned}
c < 2&\Longrightarrow\lambda_Q^{\mathrm{mix}}\longrightarrow\infty,\\
c\ge 2&\Longrightarrow\lambda_Q^{\mathrm{mix}}\longrightarrow0.
\end{aligned}
```

Para $c < 2$, a divergência é polinomial, então o limite de janela vazia é
somável e toda janela quadrada suficientemente grande é não vazia quase
certamente sob a premissa de uniformidade espacial.

<a id="44-adversarialrandom-parent-head-boundary"></a>

### 4.4 Fronteira de Cabeça para Pais Adversariais/Aleatórios

A cabeça contém apenas uma posição distinguida, então não recebe reserva
quadrática de janela. Sob marginais uniformes na cabeça, sua probabilidade de
ocorrência é a própria densidade local sobrevivente. Para transformar uma soma
divergente dessas probabilidades em recorrência quase certa, também exigimos
independência ou um substituto de mistura fraca suficientemente forte.

```math
\Pr(H_Q)
\asymp
\delta_Q^{\mathrm{mix}}
\asymp
\frac{C}{(\log Q)^2}e^{-A(Q)}.
```

Sob mistura adequada entre camadas, o segundo lema de Borel-Cantelli dá

```math
\sum_{Q\text{ prime}}\Pr(H_Q)=\infty
\Longrightarrow
H_Q\text{ ocorre infinitas vezes quase certamente}.
```

Para $\alpha_r= c/r$,

```math
\Pr(H_Q)\asymp\frac{C}{(\log Q)^{2+c}},
```

e a soma sobre primos $Q$ diverge para todo $c$ fixo. O decaimento recíproco é,
portanto, compatível com infinitos eventos de cabeça sob mistura.

Para $\alpha_r= c\log r/r$,

```math
\Pr(H_Q)\asymp\frac{C}{Q^c(\log Q)^2}.
```

Usando a densidade prima $dQ/\log Q$, a série correspondente tem o mesmo
comportamento de convergência que

```math
\int^\infty\frac{dx}{x^c(\log x)^3}.
```

Portanto

```math
\begin{aligned}
c < 1
&\Longrightarrow
\sum_{Q\text{ prime}}\Pr(H_Q)=\infty,\\
c\ge 1
&\Longrightarrow
\sum_{Q\text{ prime}}\Pr(H_Q) < \infty.
\end{aligned}
\qquad[\text{C.Q.D.}]
```

Para $c < 1$, mistura adequada implica infinitos eventos de cabeça quase
certamente. Para $c\ge 1$, o primeiro lema de Borel-Cantelli implica apenas
finitos eventos de cabeça quase certamente; nenhuma hipótese de independência é
necessária para essa direção convergente.

O limiar da cabeça $c=1$ é mais estrito que o limiar da janela segura $c=2$.
Há um regime intermediário

```math
1\le c < 2
```

no qual janelas seguras pelo quadrado permanecem povoadas quase certamente sob o
modelo espacial, enquanto a recorrência na cabeça falha quase certamente no
companheiro misto.

<a id="45-adversarialrandom-parent-phase-diagram"></a>

### 4.5 Diagrama de Fases para Pais Adversariais/Aleatórios

Para a programação representativa $\alpha_r= c\log r/r$, o companheiro se
separa em três regimes:

| Escala adversarial | Lacunas 2 globais | Janelas seguras pelo quadrado | Recorrência na cabeça |
|---|---:|---:|---:|
| $0\le c < 1$ | Persistem e crescem | Eventualmente não vazias quase certamente | Infinitas quase certamente, com mistura |
| $1\le c < 2$ | Persistem e crescem | Eventualmente não vazias quase certamente | Apenas finitas quase certamente |
| $c\ge 2$ | Persistem e crescem | Esperança mista tende a zero | Apenas finitas quase certamente |
| $\alpha > 0$ fixo | Persistem e crescem | Esperança mista tende a zero | Apenas finitas quase certamente |

As duas últimas colunas da tabela são afirmações dentro do modelo espacial. A
coluna global é incondicional para todo companheiro balanceado.

<a id="46-why-a-fixed-absolute-percentage-gives-the-wrong-maximum"></a>

### 4.6 Por que uma Porcentagem Absoluta Fixa Dá o Máximo Errado

Dentro de misturas repetidas cegas à posição, porcentagens que não mudam com o
primo do filtro têm uma resposta direta, mas secundária. Se a mesma parcela
adversarial absoluta $\alpha$ é aplicada em todo filtro, todo $\alpha > 0$ é
eventualmente fatal para a base mista local. Nessa normalização restrita,

```math
\text{parcela adversarial absoluta fixa máxima sustentável}=0\%.
```

Esta não é a resposta significativa para “quão pior que o aleatório o filtro
pode ser?” A própria destruição aleatória encolhe como $2/r$, enquanto
$\alpha > 0$ fixo adiciona um piso positivo e faz o fator relativo
$w_r=1+(r-2)\alpha/2$ divergir linearmente. A resposta primária de [§3.6](#36-relative-to-random-phase-diagram) é, em vez disso,
que todo $w$ finito fixo sobrevive ao modelo companheiro definido acima, com a
primeira transição apenas quando $w_r$ cresce na ordem de $\log r$.

A afirmação de zero por cento diz respeito à sobrevivência em janela segura e na
cabeça sob essa política de parcela absoluta fixa. Ela não diz respeito à
população global, que sobrevive até sob seleção adversarial de $100\%$.

Adversarialidade não nula permanece suportável quando sua parcela decresce com
$r$. Para uma margem fixa $\varepsilon > 0$, as programações suficientes
representativas são

```math
\begin{aligned}
\alpha_r
&\le(2-\varepsilon)\frac{\log r}{r}
&&[\text{Regime de Janela Quadrada}],\\
\alpha_r
&\le(1-\varepsilon)\frac{\log r}{r}
&&[\text{Regime de Recorrência na Cabeça, com Mistura}].
\end{aligned}
```

Ignorando a margem estrita exigida apenas para exibir as curvas de fronteira,
isso se torna

```math
\begin{aligned}
\text{porcentagem de fronteira da janela quadrada}
&=200\frac{\log r}{r}\%,\\
\text{porcentagem de fronteira da recorrência na cabeça}
&=100\frac{\log r}{r}\%.
\end{aligned}
```

Aqui $\log$ é o logaritmo natural. Valores representativos são:

| Primo de filtro $r$ | Fronteira da janela quadrada | Fronteira da recorrência na cabeça |
|---:|---:|---:|
| $101$ | $9.14\%$ | $4.57\%$ |
| $1{,}000$ | $1.38\%$ | $0.691\%$ |
| $19{,}000$ | $0.104\%$ | $0.0519\%$ |
| $100{,}003$ | $0.0230\%$ | $0.0115\%$ |

Essas entradas são valores assintóticos de fronteira, não permissões
independentes que reiniciam em cada filtro. Uma programação pode cruzar
temporariamente um valor exibido e permanecer viável se gastou menos orçamento
adversarial antes; ela também pode falhar apesar de ficar abaixo de entradas
isoladas se seu comportamento cumulativo for pior em outros filtros. As
quantidades governantes continuam sendo

```math
A(Q)=\sum_{r < Q}-\log(1-\alpha_r)
```

para janelas quadradas e

```math
\sum_{Q\text{ prime}}
\frac{e^{-A(Q)}}{(\log Q)^2}
```

para recorrência na cabeça.

<a id="47-what-percentage-adversarial-must-specify"></a>

### 4.7 O que “Porcentagem Adversarial” Precisa Especificar

Não há mistura única até especificarmos o que recebe o rótulo adversarial.

| Mistura | Escolha feita | Consequência |
|---|---|---|
| Nível do pai | Cada pai é adversarial com probabilidade $\alpha_r$ | Interpretação de ramificação independente |
| Filtro inteiro | O filtro completo é adversarial com probabilidade $\alpha_r$ | Mesma marginal de uma linhagem, dependência mais forte entre pais |
| Final único | Uma diluição adversarial é aplicada após filtragem aleatória | Um fator $1-\alpha$; nenhuma transição de fase cumulativa |

Os cálculos em §§[3](#3-relative-hazard-and-survival-frontiers)--[4](#4-absolute-share-mixtures) dizem respeito a uma parcela repetida em todo filtro. Suas
esperanças se aplicam às duas primeiras interpretações porque uma linhagem tem a
mesma probabilidade marginal de sobrevivência. Suas conclusões quase certas não
se transferem automaticamente: uma escolha de filtro inteiro coordena todos os
pais e, portanto, precisa de seu próprio argumento espacial ou de mistura. O
modelo de uma vez só responde a uma pergunta diferente porque aplica a perda
apenas uma vez.

<a id="5-allocation-and-the-protective-parent"></a>

## 5. Alocação e o Pai Protetor

<a id="51-the-same-adversarial-percentage-can-produce-different-outcomes"></a>

### 5.1 A Mesma Porcentagem Adversarial Pode Produzir Resultados Diferentes

Esta propriedade é uma comparação de capacidade. Suponha que $K$ pais possam
usar a política adversarial e que $L$ pais contribuam um filho para a janela
alvo. Um alocador ciente do alvo pode limpar a janela exatamente quando seu
orçamento cobre todos os pais relevantes:

```math
K\ge L.
```

Para uma parcela adversarial fixa $\alpha=K/N>0$, se a fração relevante
$L/N\longrightarrow0$, então eventualmente

```math
\alpha\ge\frac LN,
```

que é a mesma condição que $K\ge L$. Assim, uma porcentagem adversarial fixa
pode ser suficiente para suprimir cedo a cabeça e, depois que a população alvo
fica suficientemente esparsa, remover toda lacuna 2 da janela rastreada. O
resultado depende da alocação: um alocador cego à posição com a mesma
porcentagem não seleciona automaticamente todos os $L$ pais relevantes.

Agora derivamos o intervalo finito completo. A janela alvo é menor que o período
antigo, então cada pai contribui no máximo um filho para ela. Seja

- $N$ o número total de pais;
- $R$ o conjunto de pais com um filho na região alvo $W$;
- $L=|R|$;
- $\mathcal A$ o conjunto de pais adversariais; e
- $K=|\mathcal A|$.

Neste experimento de alocação, todo pai fora de $\mathcal A$ é protetor: ele
preserva seu filho-alvo. Assim, as únicas perdas do alvo vêm de pais
adversariais. Um complemento aleatório adicionaria perdas adicionais e não
satisfaria a identidade de sobreviventes a seguir. O número destruído é

```math
H=|\mathcal A\cap R|,
```

e o número sobrevivente é

```math
S=L-H.
```

O tamanho da interseção obedece aos limites agudos

```math
\begin{aligned}
H
&\le\min(K,L)
&&[\text{A Interseção Não Pode Exceder Nenhum dos Conjuntos}],\\
H
&\ge\max(0,K-(N-L))
&&[\text{Existem Apenas }N-L\text{ Pais Irrelevantes}].
\end{aligned}
```

Substituir em $S=L-H$ dá

```math
\max(0,L-K)
\le S\le
\min(L,N-K).
```

Ambos os extremos são atingíveis. Um alocador ciente do alvo gasta seu
orçamento primeiro em $R$:

```math
S_{\mathrm{targeted}}=\max(0,L-K).
```

Um alocador protetor gasta o mesmo orçamento primeiro nos $N-L$ pais
irrelevantes:

```math
S_{\mathrm{protective}}=\min(L,N-K).
```

Entre esses extremos, um alocador cego à posição escolhe um subconjunto
uniformemente aleatório de tamanho $K$ dos $N$ pais. Então

```math
H\sim\text{Hypergeometric}(N,L,K)
```

e

```math
\begin{aligned}
\mathbb E[H]&=\frac{KL}{N},\\
\mathbb E[S]&=L\left(1-\frac KN\right).
\end{aligned}
```

Quando $K\ge L$, a probabilidade exata de destruição local total é

```math
\Pr(S=0)
=
\frac{\binom{N-L}{K-L}}{\binom NK}
=
\frac{\binom KL}{\binom NL}.
```

Assim, o mesmo orçamento pode produzir proteção completa, perda proporcional
média ou destruição local total. Em particular,

```math
S_{\mathrm{targeted}}=0
\Longleftrightarrow
K\ge L
\Longleftrightarrow
\alpha\ge\frac LN.
\qquad[\text{C.Q.D.}]
```

As três escalas não devem ser confundidas. Na cabeça, $L=1$, então um pai
adversarial corretamente alocado mata o candidato atual na cabeça. Em uma janela
rastreada esparsa, uma parcela fixa limpa a janela inteira assim que $K\ge L$.
Nenhuma das afirmações apaga a população de lacunas 2 em período completo: todo
pai direcionado ainda deixa $r-2$ outros descendentes fora do alvo, então a
recorrência global de [§3.1](#31-global-persistence-is-independent-of-allocation) continua a crescer. Impedir lacunas 2 futuras
na cabeça ou na janela, portanto, exige que o alocador repita a escolha
direcionada em filtros posteriores.

A prova finita completa aparece no [Apêndice A.6](#appendix-a6).

<a id="52-the-protective-parent-policy"></a>

### 5.2 A Política do Pai Protetor

A política do pai protetor é o oposto local da política do pai adversarial. Ela
preserva o filho-alvo de um pai sempre que a regra de exatamente duas deleções
permite essa escolha. Ela não cria descendentes extras e não pode mudar a
recorrência global.

Para o pai $g$, seja $T_g(W)$ o conjunto dos índices de seus filhos na região
alvo $W$. No regime pós-cruzamento,

```math
|T_g(W)|\le1.
```

Como $r\ge5$, pelo menos $r-1\ge4$ índices de filhos estão fora de $T_g(W)$. A
política do pai protetor pode, portanto, escolher um par prejudicial

```math
K_{g,r}^{\mathrm{protective}}
\subseteq
(\mathbb Z/r\mathbb Z)\setminus T_g(W),
\qquad
|K_{g,r}^{\mathrm{protective}}|=2.
```

A política do pai adversarial, em vez disso, escolhe um par contendo o índice
alvo sempre que $T_g(W)$ é não vazio. Ambas as políticas removem exatamente dois
filhos, então ambas deixam $r-2$ descendentes globalmente. Sua única diferença é
o posicionamento local:

```math
\begin{aligned}
T_g(W)\ne\varnothing
&\Longrightarrow
\text{o pai protetor preserva o filho-alvo},\\
T_g(W)\ne\varnothing
&\Longrightarrow
\text{o pai adversarial destrói o filho-alvo}.
\end{aligned}
```

O pai protetor é uma comparação-oráculo, não um filtro aleatório plausível. Ele
tem permissão para ver o alvo escolhido e colocar suas duas deleções em outro
lugar. Seu propósito é definir o extremo protetor da mesma família balanceada na
qual o pai adversarial define o extremo pessimista.

<a id="53-fixed-cohort-survival-under-adversarialprotective-parent-mixing"></a>

### 5.3 Sobrevivência de Coorte Fixa sob Mistura de Pais Adversariais/Protetores

Em seguida alternamos as duas políticas extremas cientes do alvo sem deixar o
alocador inspecionar posições atuais. Considere $N_0$ linhagens localmente
relevantes de pais iniciais distintos, acompanhando um filho-alvo por pai ao
longo da cadeia. Essas histórias não compartilham pais subsequentes. No filtro
$r$, toda linhagem sobrevivente torna-se independentemente um pai adversarial
com probabilidade $\alpha_r$ ou um pai protetor com probabilidade
$1-\alpha_r$. A política adversarial destrói seu filho-alvo; a política
protetora o preserva. O cálculo muda se o alocador puder primeiro observar quais
pais são localmente relevantes.

Uma linhagem sobrevive à cadeia completa com probabilidade

```math
\begin{aligned}
P_Q
&=\prod_{r < Q}(1-\alpha_r)
&&[\text{Sobrevive a Todo Rótulo Independente de Filtro}]\\
&=e^{-A(Q)}.
&&[\text{Definição de }A(Q)]
\end{aligned}
```

A independência entre linhagens parentais então dá

```math
X_Q\sim\text{Binomial}(N_0,P_Q),
```

então

```math
\begin{aligned}
\mathbb E[X_Q]&=N_0e^{-A(Q)},\\
\Pr(X_Q > 0)&=1-\left(1-e^{-A(Q)}\right)^{N_0}.
\end{aligned}
```

Para um filtro, isso se reduz a

```math
X_{k+1}\mid X_k=N
\sim
\text{Binomial}(N,1-\alpha_r),
```

com probabilidade de aniquilação imediata $\alpha_r^N$. A redundância
populacional é, portanto, útil sob atribuição cega de pais: toda linhagem
relevante precisa se tornar um pai adversarial na mesma transição para apagar a
coorte.

Se $\alpha_r=\alpha > 0$ é constante, então

```math
P_Q=(1-\alpha)^{\pi(Q)+O(1)}\longrightarrow0.
```

Cada uma das finitas $N_0$ linhagens eventualmente se torna um pai adversarial
com probabilidade um. Logo, a coorte fixa se extingue quase certamente, embora
toda linhagem continue a ter $r-2$ descendentes em outro lugar no período
completo.

Comparada com a mistura adversarial/aleatória, a lei adversarial/protetora
remove o fator aleatório $1-2/r$:

```math
\begin{aligned}
s_r^{\mathrm{adversarial/random}}
&=(1-\alpha_r)\left(1-\frac2r\right),\\
s_r^{\mathrm{adversarial/protective}}
&=1-\alpha_r.
\end{aligned}
\qquad[\text{C.Q.D.}]
```

Essa melhoria é local. Ela não supera uma parcela adversarial positiva fixa
repetida através de infinitos filtros.

<a id="54-growing-square-windows-under-adversarialprotective-parent-mixing"></a>

### 5.4 Janelas Quadradas Crescentes sob Mistura de Pais Adversariais/Protetores

A política protetora remove a penalidade de densidade aleatória balanceada ao
preservar todo filho-alvo elegível. Suponha que o modelo totalmente protetor
forneça $B(Q)\asymp C_0Q^2$ linhagens elegíveis na janela quadrada, enquanto
cada história tem a lei condicional de sobrevivência $e^{-A(Q)}$. A probabilidade
cumulativa de rótulo adversarial é então a única perda local marginal.

De [§5.3](#53-fixed-cohort-survival-under-adversarialprotective-parent-mixing), cada uma das $B(Q)$ linhagens elegíveis sobrevive com
probabilidade $e^{-A(Q)}$. Se suas histórias completas de alvo são
independentes, então

```math
X_Q^{\mathrm{adversarial/protective}}
\sim
\text{Binomial}\left(B(Q),e^{-A(Q)}\right)
```

e

```math
\begin{aligned}
\lambda_Q^{\mathrm{adversarial/protective}}
&:=\mathbb E[X_Q^{\mathrm{adversarial/protective}}]\\
&=B(Q)e^{-A(Q)}\\
&\asymp C_0Q^2e^{-A(Q)}.
\end{aligned}
```

Sob essa hipótese adicional de independência, a probabilidade de janela vazia
satisfaz

```math
\begin{aligned}
\Pr(X_Q^{\mathrm{adversarial/protective}}=0)
&=\left(1-e^{-A(Q)}\right)^{B(Q)}\\
&\le e^{-\lambda_Q^{\mathrm{adversarial/protective}}}.
&&[1-x\le e^{-x}]
\end{aligned}
```

Rótulos independentes em pais individuais não estabelecem independência de
histórias terminais que compartilham ancestrais. O modelo binomial aqui é um
experimento local adicional, não uma consequência apenas da ramificação
balanceada. Para as conclusões de ocupação abaixo, basta em vez disso assumir
diretamente o limite de posicionamento cego
$\Pr(X_Q=0)\le e^{-\lambda_Q}$; a fórmula da esperança usa apenas a lei marginal
de sobrevivência.

Tomar logaritmos dá a fronteira de fase

```math
\log\lambda_Q^{\mathrm{adversarial/protective}}
=2\log Q-A(Q)+O(1).
```

Logo, para todo $\varepsilon > 0$ fixo,

```math
\begin{aligned}
A(Q)\le(2-\varepsilon)\log Q
&\Longrightarrow
\lambda_Q^{\mathrm{adversarial/protective}}\longrightarrow\infty,\\
A(Q)\ge(2+\varepsilon)\log Q
&\Longrightarrow
\lambda_Q^{\mathrm{adversarial/protective}}\longrightarrow0.
\end{aligned}
```

No primeiro regime, a esperança cresce polinomialmente, as probabilidades de
janela vazia são somáveis e o primeiro lema de Borel-Cantelli dá apenas finitas
janelas quadradas vazias quase certamente.

Para a programação representativa

```math
\alpha_r= c\frac{\log r}{r},
```

temos $A(Q)=c\log Q+O(1)$ e, portanto,

```math
\lambda_Q^{\mathrm{adversarial/protective}}\asymp C_0Q^{2-c}.
```

Assim

```math
\begin{aligned}
c < 2
&\Longrightarrow
\text{janelas quadradas eventualmente não vazias quase certamente},\\
c=2
&\Longrightarrow
\text{população esperada crítica de ordem um},\\
c > 2
&\Longrightarrow
\text{população esperada tende a zero}.
\end{aligned}
```

O limiar principal $c=2$ coincide com o companheiro adversarial/aleatório, mas o
termo de fronteira difere:

```math
\begin{aligned}
\lambda_Q^{\mathrm{adversarial/random}}
&\asymp C\frac{Q^{2-c}}{(\log Q)^2},\\
\lambda_Q^{\mathrm{adversarial/protective}}
&\asymp C_0Q^{2-c}.
\end{aligned}
\qquad[\text{C.Q.D.}]
```

Em $c=2$, a mistura aleatória tende a zero enquanto a mistura protetora retém
apenas uma esperança de ordem um, ainda insuficiente para não vacuidade
eventual quase certa.

<a id="55-head-recurrence-under-adversarialprotective-parent-mixing"></a>

### 5.5 Recorrência na Cabeça sob Mistura de Pais Adversariais/Protetores

Na cabeça, a política protetora pode preservar uma linhagem elegível, mas não
pode criar uma. Seja $b_Q$ sua probabilidade de disponibilidade e suponha
$b_Q\ge b > 0$ para todo $Q$ suficientemente grande. Condicionalmente à
disponibilidade, a linhagem precisa evitar toda atribuição adversarial em sua
cadeia. Independência ou mistura fraca adequada entre eventos de cabeça então
fornece o passo de recorrência.

```math
\Pr(H_Q)=b_Qe^{-A(Q)}.
```

O limite inferior em $b_Q$ torna o critério de recorrência equivalente, até
constantes positivas, a

```math
\sum_{Q\text{ prime}}e^{-A(Q)}.
```

Sob mistura adequada entre camadas, o segundo lema de Borel-Cantelli dá

```math
\sum_{Q\text{ prime}}e^{-A(Q)}=\infty
\Longrightarrow
H_Q\text{ ocorre infinitas vezes quase certamente}.
```

Se a série converge, o primeiro lema de Borel-Cantelli dá apenas finitos eventos
de cabeça quase certamente sem qualquer premissa de independência.

Para

```math
\alpha_r= c\frac{\log r}{r},
```

temos $e^{-A(Q)}\asymp Q^{-c}$. A série sobre cabeças primas, portanto, se
comporta como

```math
\sum_{Q\text{ prime}}\frac1{Q^c}.
```

A série harmônica dos primos diverge em $c=1$, enquanto a série converge para
$c > 1$. Logo

```math
\begin{aligned}
c\le1
&\Longrightarrow
\text{infinitos eventos de cabeça quase certamente, com mistura},\\
c > 1
&\Longrightarrow
\text{apenas finitos eventos de cabeça quase certamente}.
\end{aligned}
```

A fronteira difere da mistura adversarial/aleatória. Ali, a densidade de cabeça
aleatória balanceada contribui com $(\log Q)^{-2}$:

```math
\begin{aligned}
\Pr(H_Q^{\mathrm{adversarial/random}})
&\asymp\frac1{Q^c(\log Q)^2},\\
\Pr(H_Q^{\mathrm{adversarial/protective}})
&\asymp\frac{b_Q}{Q^c}.
\end{aligned}
\qquad[\text{C.Q.D.}]
```

Em $c=1$, a série prima adversarial/aleatória converge, enquanto a série
adversarial/protetora diverge. Assim, a política do pai protetor muda a inclusão
da fronteira crítica, embora ambas as misturas tenham a mesma escala de limiar
principal.

Para a programação mais branda $\alpha_r= c/r$, a probabilidade de ocorrência é
comparável a $(\log Q)^{-c}$ e a soma sobre cabeças primas diverge para todo
$c$ finito fixo.

<a id="56-parent-mixture-comparison"></a>

### 5.6 Comparação de Misturas Parentais

Sob suas respectivas premissas espaciais, as duas misturas cegas à posição têm o
seguinte comportamento assintótico:

| Programação adversarial | Janela quadrada adversarial/aleatória | Janela quadrada adversarial/protetora | Cabeça adversarial/aleatória | Cabeça adversarial/protetora |
|---|---:|---:|---:|---:|
| $\alpha > 0$ fixo | Esperança tende a zero | Esperança tende a zero | Finitas quase certamente | Finitas quase certamente |
| $\alpha_r= c/r$ | Eventualmente não vazia quase certamente | Eventualmente não vazia quase certamente | Infinita com mistura | Infinita com mistura |
| $\alpha_r= c\log r/r$, $c < 1$ | Eventualmente não vazia quase certamente | Eventualmente não vazia quase certamente | Infinita com mistura | Infinita com mistura |
| $\alpha_r= c\log r/r$, $c=1$ | Eventualmente não vazia quase certamente | Eventualmente não vazia quase certamente | Finitas quase certamente | Infinita com mistura |
| $\alpha_r= c\log r/r$, $1 < c < 2$ | Eventualmente não vazia quase certamente | Eventualmente não vazia quase certamente | Finitas quase certamente | Finitas quase certamente |
| $\alpha_r= c\log r/r$, $c=2$ | Esperança tende a zero | Esperança de ordem um | Finitas quase certamente | Finitas quase certamente |
| $\alpha_r= c\log r/r$, $c > 2$ | Esperança tende a zero | Esperança tende a zero | Finitas quase certamente | Finitas quase certamente |

A política do pai protetor remove a perda aleatória balanceada $(\log Q)^{-2}$.
Isso não muda o limiar principal de janela quadrada $c=2$, porque a janela
quadrática domina fatores logarítmicos longe da fronteira. Ela muda o
comportamento na fronteira e, mais visivelmente, inclui $c=1$ no lado recorrente
da transição na cabeça.

Toda entrada assume rótulos adversariais cegos à posição. Um alocador ciente do
alvo é governado por [§5.1](#51-the-same-adversarial-percentage-can-produce-different-outcomes) em vez disso e pode apagar a cabeça com um
rótulo adversarial corretamente colocado, independentemente do regime percentual
desta tabela.

<a id="6-allocation-mechanisms-and-local-damage"></a>

## 6. Mecanismos de Alocação e Dano Local

<a id="61-mechanism-families"></a>

### 6.1 Famílias de Mecanismos

Uma parcela adversarial só se torna significativa depois que dizemos como as
políticas são atribuídas aos pais. Uma comparação útil começa com um alocador
cego à posição e então adiciona informação posicional em passos controlados.
Escrevemos $P$ para um pai protetor e $A$ para um pai adversarial.

| Mecanismo | Parcela adversarial | Informação posicional | O que mede |
|---|---:|---:|---|
| Moeda parental independente | Aleatória em torno de $\alpha_r$ | Nenhuma | Lei de ramificação mais simples |
| Embaralhamento de quota exata | Exatamente $K/N$ | Nenhuma | Base canônica de população finita |
| Alternância embaralhada, $P,A,P,A,\ldots$ | Fixada pelo padrão | Nenhuma | Rótulos determinísticos balanceados após embaralhamento |
| Embaralhamento balanceado por blocos | Fixada dentro de cada bloco | Nenhuma | Sensibilidade a agrupamento local |
| Máscara cíclica aleatória | Fixada pelo padrão | Nenhuma | Sensibilidade à alocação periódica |
| Hash cego à posição | Aleatória em torno de $\alpha_r$ | Nenhuma | Moedas parentais reprodutíveis |
| Adversário atrasado | Exatamente $K/N$ | Camada anterior | Persistência da informação posicional |
| Ranqueamento ruidoso | Exatamente $K/N$ | Ajustável | Transição de alocação cega para direcionada |
| Adversário perfeito | Exatamente $K/N$ | Camada atual | Extremo de pior caso |

O embaralhamento de quota exata é o modelo nulo primário porque fixa o
orçamento sem usar posição. Padrões embaralhados e balanço por blocos testam se
agrupamento local muda o resultado. Um alocador atrasado pode usar apenas a
camada anterior, enquanto ranqueamento ruidoso atribui peso $e^{-\beta d_g}$ a
um pai a distância $d_g$ do alvo. Assim, $\beta=0$ é alocação uniforme e
$\beta$ grande se aproxima do adversário perfeito.

Todo mecanismo atribui uma política a um pai; a política escolhida ainda remove
exatamente dois filhos daquele pai. Rótulos alternados não podem restaurar um
filho-alvo destruído em um filtro anterior, e um padrão periódico não
embaralhado pode se travar à geometria da peneira. Portanto, comparamos
mecanismos por meio de seu dano local realizado e força de direcionamento, em
vez de apenas pela porcentagem programada.

<a id="62-targeting-and-local-hazard"></a>

### 6.2 Direcionamento e Risco Local

O espaço de estados observado primário tem duas coordenadas:

```math
(w_r,\theta_r)
=
(\text{dano relativo ao aleatório},\text{força de direcionamento realizada}).
```

A primeira diz quanto dano total o segmento rastreado realmente recebeu. A
segunda diz quão concentrado o orçamento controlável de rótulos adversariais
foi em relação aos pais localmente relevantes. A parcela programada
$\alpha_r=K_r/N_r$ continua sendo uma entrada experimental, mas não é ela mesma
o dano local.

#### Força de Direcionamento Normalizada

Para uma transição não degenerada, mantenha a notação de [§5.1](#51-the-same-adversarial-percentage-can-produce-different-outcomes) e defina

```math
\begin{aligned}
H_{\min}&=\max(0,K-(N-L)),\\
H_0&=\frac{KL}{N},\\
H_{\max}&=\min(K,L).
\end{aligned}
```

Esses são o mínimo protetor, a média uniforme-aleatória e o máximo adversarial
do número de pais localmente relevantes atingidos. Quando
$H_{\min} < H_0 < H_{\max}$, normalize a contagem realizada de atingidos $H$ por

```math
\theta(H)=
\begin{cases}
\dfrac{H-H_0}{H_0-H_{\min}},&H\le H_0,\\[8pt]
\dfrac{H-H_0}{H_{\max}-H_0},&H\ge H_0.
\end{cases}
```

Então

```math
\begin{aligned}
\theta=-1&\Longleftrightarrow H=H_{\min}
&&[\text{Extremo Protetor}],\\
\theta=0&\Longleftrightarrow H=H_0
&&[\text{Benchmark Uniforme}],\\
\theta=1&\Longleftrightarrow H=H_{\max}
&&[\text{Extremo Direcionado}].
\end{aligned}
```

O centro $H_0$ é uma esperança e não precisa ser inteiro, então uma realização
finita não precisa atingir $\theta=0$ exatamente. Ele continua sendo o ponto de
referência neutro.

Casos degenerados com denominador zero devem reportar a tupla bruta
$(N,L,K,H)$ em vez de atribuir um escore sintético. Em todo caso, a contagem
local de sobreviventes permanece o observável exato

```math
S=L-H.
```

O escore mede posicionamento realizado, não intenção hostil. Um embaralhamento
aleatório pode ocasionalmente produzir $\theta$ positivo, e um adversário
nominal com pouca informação pode produzir $\theta$ negativo.

#### Risco Local Realizado

Seja $T_r$ o número total de filhos-alvo localmente relevantes destruídos pelo
filtro completo, incluindo tanto a destruição da base aleatória quanto a
destruição por rótulo adversarial. Defina

```math
f_r^{\mathrm{local}}=\frac{T_r}{L_r},
\qquad
w_r^{\mathrm{local}}=\frac{rT_r}{2L_r},
\qquad L_r > 0.
```

Na atribuição adversarial/protetora pura, um rótulo adversarial destrói seu alvo
e um rótulo protetor o preserva, então $T_r=H_r$. Na atribuição
adversarial/aleatória, $T_r$ também contém a base $2/r$ do ramo aleatório. Para
rótulos adversariais/aleatórios cegos,

```math
\mathbb E[f_r^{\mathrm{local}}]
\approx
\alpha_r+(1-\alpha_r)\frac2r.
```

Um adversário perfeito pode fazer $f_r^{\mathrm{local}}=1$ mesmo quando o
orçamento global $\alpha_r=K_r/N_r$ é minúsculo, desde que seu orçamento e sua
informação cubram o alvo local.

Para uma coorte aninhada fixa, o risco cumulativo observado é

```math
\widehat D(Q)
=
\sum_{r < Q}-\log\left(1-f_r^{\mathrm{local}}\right),
```

sempre que todo fator é positivo. Se uma transição tem
$f_r^{\mathrm{local}}=1$, a coorte local rastreada está extinta e
$\widehat D(Q)$ é efetivamente infinito a partir desse ponto. Esse diagnóstico
generaliza $A(Q)$ e inclui a base aleatória, em vez de contar apenas a perda
excedente por rótulo adversarial. A separação entre $\alpha_r$ programado,
$w_r^{\mathrm{local}}$ realizado e escore de direcionamento $\theta_r$ mede,
respectivamente, orçamento de política, dano relativo total e o valor da
informação posicional.

Quando a população localmente relevante é redefinida em toda transição, em vez
de seguir uma coorte, $\widehat D(Q)$ é apenas um diagnóstico cumulativo; não é
um expoente exato de sobrevivência para uma única população.

Podemos, portanto, ler os cálculos de fase anteriores com três níveis de
entrada:

- $A(Q)$ é o orçamento programado sob o modelo de alocação cega;
- $\widehat D(Q)$ registra o dano observado ao longo de uma coorte especificada; e
- $\theta_r$ registra quão fortemente o orçamento controlável direcionou o segmento.

Somente o primeiro tem forma fechada a partir de $\alpha_r$ sozinho. O diagrama
de fases probabilístico usa riscos condicionais $D(Q)$ e $w_r$. Aplicá-lo aos
escores observados exige um teorema que relacione esses escores às marginais dos
candidatos.

<a id="63-comparing-the-allocation-mechanisms"></a>

### 6.3 Comparando os Mecanismos de Alocação

Os mecanismos diferem em quanto sabem sobre o alvo, então os comparamos com o
mesmo orçamento de ataques e a mesma região alvo. Embaralhamento uniforme é a
referência neutra. Balanço por blocos e informação atrasada mostram se a
dependência sozinha muda o resultado. Ranqueamento ruidoso se move
continuamente em direção ao extremo perfeitamente direcionado.

| Alocação | Informação sobre o alvo | Papel na comparação |
|---|---|---|
| Quota exata uniforme | Nenhuma | Base aleatória |
| Quota balanceada por blocos | Nenhuma, mas localmente dependente | Teste de agrupamento |
| Alocação atrasada | Apenas camada anterior | Teste de memória |
| Ranqueamento ruidoso | Informação atual parcial | Direcionamento intermediário |
| Alocação perfeita | Informação atual completa | Extremo adversarial |

Para cada transição, a observação essencial é a tupla

```math
(N_r,L_r,K_r,H_r,T_r,w_r^{\mathrm{local}},\theta_r).
```

Ela registra os pais totais e localmente relevantes, o orçamento adversarial
disponível, o número de pais relevantes selecionados, a destruição local total,
o dano relativo ao aleatório e o escore de direcionamento. Companheiros de
quota exata também retêm $J_r$, $u_r=J_r/N_r^{\mathrm{strike}}$ e as somas
cumulativas

```math
\sum_{r < Q}u_r
\qquad\text{e}\qquad
\sum_{r < Q}\left(u_r^2+\frac{u_r}{N_r^{\mathrm{strike}}}\right),
```

porque igualar uma contagem finita de ataques não estabelece as condições
cumulativas usadas em [§7.1](#71-exact-crt-quotas-with-random-locations).

O filtro modular real não tem política parental atribuída, mas as mesmas
observações locais ainda se aplicam. Sua contagem de acertos pode ser comparada
com o mínimo protetor, a média uniforme e o máximo adversarial de [§6.2](#62-targeting-and-local-hazard). Ao longo de cabeças
sucessivas, $D(Q)$ então mostra se o posicionamento aritmético permanece perto
do companheiro aleatório ou acumula dano como um alocador informado. Esta é uma
comparação de comportamento, não uma atribuição de intenção.

<a id="7-exact-quota-companion-processes"></a>

## 7. Processos Companheiros de Quota Exata

<a id="71-exact-crt-quotas-with-random-locations"></a>

### 7.1 Quotas CRT Exatas com Localizações Aleatórias

O modelo de pai aleatório fixa dois índices de cópia prejudiciais por pai. Um
companheiro estatístico separado, em vez disso, retém o número exato de ataques
aceitos fornecido por uma população CRT escolhida e aleatoriza apenas suas
localizações. Isso preserva a contagem real enquanto remove a informação
aritmética de direcionamento, mas não preserva duas perdas por pai de lacuna 2
nem a recorrência global balanceada. Quotas exatas criam dependência dentro de
uma camada, mas não mudam a escala de sobrevivência de uma posição quando
alocadas uniformemente na população elegível condicionada. O resultado da cabeça
também usa disponibilidade persistente e mistura entre camadas, enquanto o
resultado de janela quadrada usa posicionamento cego e suprimento elegível
quadrático.

No filtro $r$, seja $U_r$ contendo $N_r$ valores elegíveis e seja $J_r$ a quota
CRT, com $0\le J_r\le N_r-2$. O modelo de pai aleatório com quota exata escolhe
um subconjunto uniformemente aleatório de tamanho $J_r$ de $U_r$ como seu
conjunto de ataques. Para uma lacuna 2 especificada cujos dois extremos
pertencem a $U_r$, ambos os extremos sobrevivem precisamente quando todo ataque
é selecionado dos outros $N_r-2$ valores. Portanto

```math
\begin{aligned}
s_r
&=\frac{\binom{N_r-2}{J_r}}{\binom{N_r}{J_r}}
&&[\text{Escolha Uniforme de Quota Exata}]\\
&=\frac{(N_r-J_r)(N_r-J_r-1)}{N_r(N_r-1)}.
&&[\text{Simplificação Fatorial}]
\end{aligned}
```

Escreva a fração de ataques como

```math
u_r:=\frac{J_r}{N_r}.
```

A fórmula exata dá

```math
\log s_r
=-2u_r+O\left(u_r^2+\frac{u_r}{N_r}\right).
```

Isso separa a quota finita exata da condição cumulativa necessária para a
recorrência. Assuma que ao longo da cadeia condicionada até a cabeça $Q$,

```math
\begin{aligned}
\sum_{r < Q}u_r
&=\log\log Q+O(1),
&&[\text{Quota Cumulativa na Taxa CRT}]\\
\sum_{r < Q}
\left(u_r^2+\frac{u_r}{N_r}\right)
&=O(1).
&&[\text{Erro Somável de População Finita}]
\end{aligned}
```

O benchmark CRT de período completo $u_r=1/r$ satisfaz essas condições. Uma
quota CRT local diferente precisa ser checada contra elas; preservar apenas uma
contagem numérica de ataques não torna a conclusão automática.

Multiplicar os fatores exatos sem reposição dá

```math
\begin{aligned}
P_{\mathrm{quota}}(Q)
&=\prod_{r < Q}s_r
&&[\text{Sobrevive a Todo Filtro}]\\
&=\exp\left(\sum_{r < Q}\log s_r\right)
&&[\text{Produto para Soma}]\\
&=\exp\left(-2\sum_{r < Q}u_r+O(1)\right)
&&[\text{Erro Somável}]\\
&\asymp\frac{C}{(\log Q)^2}.
&&[\text{Condição Cumulativa de Quota}]
\end{aligned}
```

Assim, o companheiro de quota exata tem a mesma ordem de sobrevivência em uma
cabeça que o modelo de pai aleatório. Ele não é um filtro de Bernoulli
independente dentro de uma camada; é um embaralhamento uniforme condicionado à
contagem exata de ataques CRT.

Suponha que o candidato distinguido na cabeça seja elegível com probabilidade
condicional pelo menos $b_0 > 0$, uniformemente para todas as cabeças primas
suficientemente grandes, e que essa disponibilidade seja compatível com o
experimento de sobrevivência por quota. Então

```math
\begin{aligned}
b_0P_{\mathrm{quota}}(Q)
&\le\Pr(H_Q)\le P_{\mathrm{quota}}(Q),
&&[\text{Limites Uniformes de Disponibilidade}]\\
\Pr(H_Q)
&\asymp\frac{1}{(\log Q)^2}.
&&[\text{Assintótica de Sobrevivência por Quota}]
\end{aligned}
```

Consequentemente,

```math
\begin{aligned}
\sum_{Q\text{ prime}}\Pr(H_Q)
&\asymp
\sum_{Q\text{ prime}}\frac{1}{(\log Q)^2}\\
&=\infty.
&&[\text{Teorema dos Números Primos}]
\end{aligned}
```

Sob independência ou uma condição adequada de mistura entre camadas, o segundo
lema de Borel-Cantelli produz

```math
\Pr(H_Q\text{ ocorre infinitas vezes})=1.
\qquad[\text{C.Q.D.}]
```

Este é um teorema quase certo, não uma garantia para toda realização aleatória.
O conjunto de realizações com apenas finitos acertos na cabeça tem probabilidade
zero, mas não é logicamente vazio.

Para janelas seguras pelo quadrado, assuma $B(Q)\asymp C_0Q^2$ inícios
elegíveis e a mesma premissa de posicionamento cego para janela vazia usada
pelo modelo de pai aleatório. Então

```math
\begin{aligned}
\lambda_{\mathrm{quota}}(Q)
&=B(Q)P_{\mathrm{quota}}(Q)
&&[\text{Inícios Sobreviventes Esperados}]\\
&\asymp
C_0\frac{Q^2}{(\log Q)^2}
\longrightarrow\infty.
&&[\text{Suprimento Quadrático Domina}]
\end{aligned}
```

Se

```math
\Pr(W_Q\text{ is empty})
\le e^{-\lambda_{\mathrm{quota}}(Q)},
```

as probabilidades de vazio são somáveis sobre primos $Q$. O primeiro lema de
Borel-Cantelli então dá apenas finitas janelas quadradas vazias quase
certamente. Essa afirmação de janela eventual é mais forte que o alvo no estilo
dos primos gêmeos: uma sequência ilimitada de janelas bem-sucedidas, ou
infinitos acertos na cabeça, já é suficiente para infinitos certificados
distintos.

Para primos consecutivos $p < q$, a contagem real de ataques aceitos na próxima
janela segura é provada em [Dinâmica de Lacunas §9.1](https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter6/gap-dynamics.md#91-exact-accepted-strikes) [[2]](#ref2):

```math
A(p,q)
=
\pi\left(\left\lfloor\frac{q^2-1}{p}\right\rfloor\right)
-\pi(p-1).
```

Usar essa quota local como $J_r=A(p,q)$ no companheiro de localização aleatória
é bem definido, mas suas frações $u_r=J_r/N_r$ ainda precisam satisfazer as
condições cumulativas exibidas para a prova de cabeça acima. A [contagem de período completo](https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter6/gap-dynamics.md#52-exact-non-recursive-global-count) [[2]](#ref2) fornece a
densidade global; nenhuma contagem exata determina o posicionamento local na
peneira real.

<a id="72-biased-exact-quotas-and-the-logarithmic-skew-frontier"></a>

### 7.2 Quotas Exatas Enviesadas e a Fronteira Logarítmica de Viés

O companheiro neutro de quota exata trata todo valor elegível simetricamente.
Agora mantemos a mesma quota $J_r$ enquanto tornamos os extremos de lacunas 2
proporcionalmente mais propensos a receber um ataque prejudicial. Isso pergunta
quanta preferência posicional a quota pode carregar antes que a conclusão quase
certa sobre a cabeça mude. Usamos uma lei de alocação trocável por grupos,
assumimos que ataques duplos em um par de extremos têm ordem quadrática e
mantemos as premissas de disponibilidade, posicionamento e mistura de
[§3.5](#35-logarithmically-growing-worsening-has-two-thresholds) e [§7.1](#71-exact-crt-quotas-with-random-locations).

Seja $E_r\subseteq U_r$ o conjunto dos valores elegíveis que são extremos de
lacunas 2 localmente relevantes, e defina

```math
x_r:=\frac{|E_r|}{N_r},
\qquad
u_r:=\frac{J_r}{N_r}.
```

Estipule uma lei de alocação de tamanho $J_r$ trocável por grupos na qual todo
extremo tem probabilidade marginal de inclusão $p_r^{E}$, todo valor ordinário
tem probabilidade marginal de inclusão $p_r^{O}$, e a razão de preferência por
extremos é

```math
\beta_r:=\frac{p_r^{E}}{p_r^{O}}\ge1.
```

Exigimos que essas marginais sejam viáveis:

```math
0\le p_r^{O},p_r^{E}\le1.
```

Essa condição, junto com a lei de tamanho fixo, é uma hipótese sobre a
construção de quota trocável por grupos, não uma consequência apenas da razão
$\beta_r$.

A quota fixa força a probabilidade marginal média de inclusão a ser igual a
$u_r$. Portanto

```math
\begin{aligned}
x_rp_r^{E}+(1-x_r)p_r^{O}
&=u_r
&&[\text{Quota Exata}]\\
p_r^{O}
&=\frac{u_r}{1+(\beta_r-1)x_r}
&&[\text{Substituição}]\\
p_r^{E}
&=\frac{\beta_ru_r}{1+(\beta_r-1)x_r}.
&&[\text{Simplificação}]
\end{aligned}
```

Defina a preferência normalizada pela quota

```math
\kappa_r^{\mathrm{eff}}
:=
\frac{\beta_r}{1+(\beta_r-1)x_r}.
```

Para uma lacuna 2, assuma que a probabilidade de ambos os extremos serem
atacados é $O((p_r^{E})^2)$. Sua fração de destruição então satisfaz

```math
\begin{aligned}
f_r
&=2p_r^{E}-\Pr(\text{both endpoints are struck})
&&[\text{Inclusão-Exclusão}]\\
&=2u_r\kappa_r^{\mathrm{eff}}
+O\left((u_r\kappa_r^{\mathrm{eff}})^2\right).
&&[\text{Preferência Normalizada}]
\end{aligned}
```

Para usar cumulativamente o termo linear exibido, exigimos adicionalmente
$p_r^E=u_r\kappa_r^{\mathrm{eff}}\to0$ e

```math
\sum_{r<\infty}\left(u_r\kappa_r^{\mathrm{eff}}\right)^2<\infty.
```

Sem esse controle de erro, a expansão por filtro não determina o risco
cumulativo assintótico.

O peso bruto $\beta_r$ e o viés efetivo de destruição não são idênticos: a quota
exata precisa retirar probabilidade de valores ordinários quando dá mais
probabilidade aos extremos. Para a população elegível da peneira em período
completo, seja $V_r$ sua contagem de valores aceitos e $T_r$ sua contagem de
lacunas 2. Após o filtro $3$, lacunas 2 têm extremos disjuntos, então
$|E_r|=2T_r$ e

```math
\begin{aligned}
x_r
&=\frac{2T_r}{V_r}\\
&=2\prod_{3\le p\lt r}\frac{p-2}{p-1}\\
&=\Theta\left(\frac1{\log r}\right).
&&[\text{Estimativa de Produto Tipo Mertens}]
\end{aligned}
```

A densidade anterior $\Theta((\log r)^{-2})$ seria a densidade entre inteiros
brutos, não entre os valores elegíveis $U_r$ usados nesta quota. Para as
assintóticas ilustrativas mais agudas

```math
x_r\sim\frac{C}{\log r},
\qquad
\beta_r\sim b\log r,
```

we instead obtain

```math
\kappa_r^{\mathrm{eff}}
=\frac{b}{1+bC}\log r\,(1+o(1)).
```

Assim, uma preferência bruta logarítmica muda seu coeficiente efetivo
principal. Uma relação esparsa $x_r=O((\log r)^{-2})$ pode ser imposta como
hipótese adicional para uma população alvo local diferente, mas não é a densidade
elegível da peneira em período completo.

Para o teorema de fases, meça o viés pelo fator efetivo realizado

```math
\kappa_r
:=\frac{f_r}{2/r}.
```

Esta é a mesma quantidade chamada $w_r$ na análise geral de risco. Sua
sobrevivência cumulativa é definida uma vez que $2\kappa_r < r$. Todo regime
abaixo satisfaz essa desigualdade para todos os filtros suficientemente grandes;
o prefixo finito é absorvido em uma constante positiva. Assim

```math
P_{\kappa}(Q)
=
\prod_{r < Q}\left(1-\frac{2\kappa_r}{r}\right)
=e^{-D_{\kappa}(Q)},
```

onde

```math
D_{\kappa}(Q)
:=
\sum_{r < Q}-\log\left(1-\frac{2\kappa_r}{r}\right).
```

If $\kappa_r=\kappa < \infty$ is fixed, then

```math
\begin{aligned}
D_{\kappa}(Q)
&=2\kappa\log\log Q+O(1)
&&[\text{Soma Harmônica dos Primos}]\\
P_{\kappa}(Q)
&\asymp\frac{C_{\kappa}}{(\log Q)^{2\kappa}}.
&&[\text{Exponenciação}]
\end{aligned}
```

A soma dessa probabilidade sobre cabeças primas diverge para todo $\kappa$
finito. Com disponibilidade persistente na cabeça e mistura adequada entre
camadas,

```math
\text{todo viés proporcional finito fixo dá infinitos acertos na cabeça quase certamente.}
```

Assim, não há máximo finito de viés constante.

A primeira transição aparece quando o viés efetivo cresce logaritmicamente.
Defina

```math
\kappa_r=1+c\log r,
\qquad c\ge0.
```

Então

```math
\begin{aligned}
D_c(Q)
&=2\log\log Q+2c\log Q+O(1)
&&[\text{Assintótica de Soma sobre Primos}]\\
P_c(Q)
&\asymp\frac{C_c}{Q^{2c}(\log Q)^2}.
&&[\text{Exponenciação}]
\end{aligned}
```

Para cabeças primas, a série de ocorrência tem o mesmo comportamento de
convergência que

```math
\int^\infty\frac{dx}{x^{2c}(\log x)^3}.
```

Portanto

```math
\begin{aligned}
c < \frac12
&\Longrightarrow
\text{infinitos acertos na cabeça quase certamente, com mistura},\\
c\ge\frac12
&\Longrightarrow
\text{apenas finitos acertos na cabeça quase certamente}.
\end{aligned}
\qquad[\text{C.Q.D.}]
```

Nesta família explicitamente normalizada, a igualdade $c=1/2$ está no lado de
falha porque o fator restante $(\log Q)^{-2}$ faz a série prima de fronteira
convergir. Se $\beta_r$, em vez de $\kappa_r$ efetivo, é especificado em sua
fronteira bruta de igualdade, a normalização por quota muda termos de ordem
menor e a série cumulativa $D_{\kappa}(Q)$ precisa ser avaliada diretamente.

A fronteira robusta segura para a cabeça é, portanto,

```math
\kappa_r
\le
1+\left(\frac12-\varepsilon\right)\log r
\quad\Longrightarrow\quad
\text{recorrência na cabeça quase certamente, com mistura}.
```

Para janelas quadradas, o suprimento quadrático dá a fronteira robusta maior

```math
\kappa_r
\le
1+(1-\varepsilon)\log r
\quad\Longrightarrow\quad
\text{ocupação eventual de janela quadrada quase certamente}.
```

Logo, o intervalo intermediário entre aproximadamente $(1/2)\log r$ e $\log r$
preserva janelas quadradas, mas não acertos na cabeça recorrendo infinitamente.
A afirmação sobre janelas é mais forte que o necessário: a conclusão no estilo
dos primos gêmeos precisa apenas de infinitas janelas bem-sucedidas.

Para uma programação irregular de viés, o critério da cabeça é

```math
\sum_{Q\text{ prime}}e^{-D_{\kappa}(Q)}=\infty,
```

junto com disponibilidade persistente e mistura adequada. Uma porcentagem
pontual de viés não pode substituir esse teste cumulativo.

<a id="8-relation-to-the-real-sieve"></a>

## 8. Relação com a Peneira Real

Para uma lacuna 2 real $(a,a+2)$ e primo entrante $r$, as cópias prejudiciais
não são escolhidas livremente. Elas são fixadas por

```math
K_{a,r}^{\mathrm{real}}
=
\{-aM^{-1},-(a+2)M^{-1}\}\pmod r.
```

Pais diferentes são acoplados por essa única regra aritmética. O filtro real
não tem moedas de política independentes nem rótulos protetores e adversariais
livremente alocados. Ainda assim, ele tem destruição local diretamente mensurável
$\widehat f_r$, um fator relativo $\widehat w_r=r\widehat f_r/2$ e, para uma
coorte fixa, risco observado $\widehat D(Q)$. Essas são as quantidades empíricas
de [§3.2](#32-local-destruction-relative-to-random), não probabilidades
atribuídas à peneira determinística. Atribuir a ela uma parcela efetiva de
política $\alpha_r$ exige um benchmark companheiro adicional declarado,
enquanto avaliar sua concentração posicional exige a contagem separada de
acertos e a normalização de direcionamento de [§6.2](#62-targeting-and-local-hazard).

O fator relativo definido em [§3.2](#32-local-destruction-relative-to-random) fornece uma normalização de destruição em
transição finita. A Seção 6.2 adiciona a pergunta de alocação: para o mesmo
orçamento global de destruição, quão próxima a contagem local realizada de
acertos fica da média uniforme ou do máximo direcionado?

Os diagramas companheiros identificam o que um teorema de transferência
precisaria controlar:

- o dano relativo observado $\widehat w_r$ e o risco de coorte fixa
  $\widehat D(Q)$, junto com um teorema separado que os relacione a riscos
  condicionais candidatos;
- as frações de quota exata $u_r$ e seu desvio cumulativo de $\sum_{r < Q}1/r$;
- preferência bruta por extremos $\beta_r$, viés efetivo normalizado por quota
  $\kappa_r^{\mathrm{eff}}$ e risco cumulativo de viés $D_{\kappa}(Q)$;
- qualquer orçamento de política programado ou efetivo $A(Q)$ usado para uma
  especialização companheira particular;
- as premissas de disponibilidade e abundância para o alvo escolhido; e
- um limite determinístico de discrepância comparando os indicadores reais de
  cabeça $I_Q$ com os pesos divergentes de referência companheira $\rho_Q$, como
  formalizado em [§10](#10-conclusion).

<a id="81-finite-empirical-comparison-with-random"></a>

### 8.1 Comparação Empírica Finita com o Aleatório

Podemos comparar a peneira real com o companheiro aleatório em duas escalas de
janela quadrada. A primeira comparação conta as lacunas 2 já presentes na
própria janela de cada sequência. Para a cabeça $h$, seja
$G_{\mathrm{real}}(h)$ o número de inícios reais de lacunas 2 em $[h,h^2)$. A
esperança do companheiro aleatório é

```math
E_{\mathrm{random}}(h)
=(h^2-h)\frac12
\prod_{3\le r < h}\left(1-\frac2r\right).
```

A fronteira de janela quadrada $c=1$ adiciona o risco excedente logarítmico de
[§3.5](#35-logarithmically-growing-worsening-has-two-thresholds):

```math
E_{c=1}(h)
=E_{\mathrm{random}}(h)
\prod_{7\le r < h}
\left(1-\frac{2\log r}{r-2}\right).
```

A figura compara essas duas esperanças com a contagem real em toda janela de
sequência completamente coberta. Ao longo de 188 cabeças de $3$ até $1129$, a
razão média $G_{\mathrm{real}}/E_{\mathrm{random}}$ é $0.967$. Na maior cabeça
coberta, ela é $0.947$: a janela real contém $10{,}056$ lacunas 2, comparada com
uma esperança aleatória de $10{,}616$. A esperança correspondente da fronteira
$c=1$ é apenas $0.0845$. Ao longo desse intervalo finito, a população real de
janela quadrada segue a escala aleatória e permanece muito acima da fronteira de
falha da janela quadrada.

![Contagens reais de lacunas 2 por sequência em janela quadrada comparadas com a esperança aleatória e a fronteira de janela quadrada c=1](https://raw.githubusercontent.com/thiagomata/prime-numbers/master/charts/per-sequence-frontier.svg)

A figura é gerada pelo [cálculo da fronteira por sequência](https://github.com/thiagomata/prime-numbers/blob/master/python/src/sieve_sequence/per_sequence_frontier_chart.py)
a partir dos [dados de sobreviventes por sequência](https://github.com/thiagomata/prime-numbers/blob/master/data/sieve-sequence/first_gaps_per_seq.csv).

A segunda comparação isola uma transição. Para primos consecutivos $p<q$, seja
$G_p$ a população de lacunas 2 pré-filtro em $[q,q^2)$ e seja $H_p$ o número
destruído quando o filtro $p$ é instalado. A fração observada e seu fator
relativo são

```math
f_p^{\mathrm{real}}:=\frac{H_p}{G_p},
\qquad
w_p^{\mathrm{real}}:=\frac{pf_p^{\mathrm{real}}}{2}.
```

O gráfico compara $f_p^{\mathrm{real}}$ com a taxa aleatória $2/p$ e a fronteira
de janela quadrada $c=1$, $2(1+\log p)/p$. Entre 187 transições medidas
distintas de $p=3$ até $p=19{,}429$, 186 ficam abaixo da taxa aleatória e a
transição restante, $p=3$, é igual a ela. Noventa e cinco transições não
destroem nenhuma lacuna 2 na janela medida. A partir de $p\ge1000$, o maior
fator relativo observado é

```math
w_p^{\mathrm{real}}=0.0523.
```

Assim, a transição real medida não é ligeiramente mais destrutiva que o filtro
aleatório; nessas janelas, ela é substancialmente menos destrutiva.

![Destruição real por transição de lacunas 2 em janela quadrada comparada com a taxa aleatória e a fronteira de janela quadrada c=1](https://raw.githubusercontent.com/thiagomata/prime-numbers/master/charts/frontier-comparison-stages.svg)

A figura é gerada pelo [cálculo da fronteira por transição](https://github.com/thiagomata/prime-numbers/blob/master/python/src/sieve_sequence/frontier_comparison_stages_chart.py)
a partir dos dados de transição [densos](https://github.com/thiagomata/prime-numbers/blob/master/data/candidates/window-measurements.csv) e
[esparsos](https://github.com/thiagomata/prime-numbers/blob/master/data/candidates/window-measurements-sparse.csv). Transições de destruição zero são exibidas no piso $10^{-7}$ do
gráfico para que permaneçam visíveis em um eixo logarítmico.

Os dois achados são compatíveis. O primeiro gráfico mede a população deixada
após todos os filtros anteriores; o segundo isola o próximo filtro agindo em uma
nova janela. Nenhum conjunto de dados segue uma coorte fixa através de todo
filtro abaixo de uma única cabeça, então suas frações de janela variável não
podem ser multiplicadas em um único risco cumulativo.

O ciclo modular completo fornece uma referência exata em duas visões
complementares. A primeira é local a um filtro: pergunta que fração da população
cíclica expandida esse filtro destrói. A segunda é cumulativa: pergunta quanto
de uma população inicial normalizada permanece depois que essas frações de um
filtro são compostas. As duas figuras abaixo espelham deliberadamente esses dois
passos do cálculo.

#### Destruição Exata por Filtro

Se $T$ lacunas 2 cíclicas antigas são expandidas através de um novo primo $r$,
há $rT$ cópias e exatamente dois índices de cópia prejudiciais por pai.
Consequentemente,

```math
\begin{aligned}
H_r^{\mathrm{cycle}}
&=2T
&&[\text{Duas Classes de Cópias Prejudiciais}],\\
f_r^{\mathrm{cycle}}
&=\frac{H_r^{\mathrm{cycle}}}{rT}
=\frac2r
&&[\text{Substituição}],\\
w_r^{\mathrm{cycle}}
&=1,
&&[\text{Pela Definição}],\\
D_{\mathrm{cycle}}(R)-D_{\mathrm{random}}(R)
&=0.
&&[\text{Igualdade Termo a Termo; C.Q.D.}]
\end{aligned}
```

Assim, a fração de destruição em ciclo completo é igual ao benchmark neutro como
identidade de contagem. Isso não diz que as posições prejudiciais são
independentemente aleatórias. A figura abaixo torna a identidade visível ao lado
da referência $c=1$ no intervalo válido $29\le r\le251$. Sua simplicidade é o
ponto: a sobreposição entre as curvas de ciclo exato e neutra é a forma gráfica
da álgebra acima, enquanto a curva $c=1$ separada mostra a escala da piora
logarítmica hipotética. O gráfico é forte precisamente porque o leitor pode
verificar a relação declarada sem interpretação adicional.

![Fração exata de destruição de lacunas 2 em ciclo completo comparada com a taxa neutra e a referência c=1](https://raw.githubusercontent.com/thiagomata/prime-numbers/master/charts/full-cycle-destruction.svg)

A figura é gerada pelo [cálculo de destruição de ciclo completo](https://github.com/thiagomata/prime-numbers/blob/master/python/src/sieve_sequence/full_cycle_destruction_chart.py).
O resultado subjacente de duas classes é provado em [Dinâmica de Lacunas §6.1](https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter6/gap-dynamics.md#61-one-new-prime-forbids-two-copy-classes) [[2]](#ref2).

#### Consequência Cumulativa de Sobrevivência

O primeiro diagrama torna visível a igualdade provada de um filtro. Compor
esses mesmos fatores dá a referência normalizada de sobrevivência em ciclo
completo

```math
\begin{aligned}
P_{\mathrm{cycle}}(29,R)
&=\prod_{29\le p\le R}\left(1-\frac2p\right),\\
P_{c=1}(29,R)
&=\prod_{29\le p\le R}
\left(1-\frac{2(1+\log p)}p\right).
\end{aligned}
```

Em $R=251$, esses produtos normalizados são $0.3733$ e $0.003676$,
respectivamente, uma razão de cerca de $102$. A segunda figura, portanto,
mostra a consequência cumulativa que a primeira figura não pode mostrar por si
só: a separação repetida por filtro em relação à programação $c=1$ se compõe em
uma separação de mais de duas ordens de grandeza ao longo do intervalo plotado.
A âncora $29$ é o primeiro primo plotado e mantém todo fator $c=1$ em $(0,1)$;
mudar uma âncora finita muda as constantes de normalização, não os expoentes
assintóticos. Esta é uma comparação de referência, não evidência de recorrência
na cabeça.

![Sobrevivência normalizada de lacunas 2 em ciclo completo sob a lei exata por filtro comparada com a programação c=1](https://raw.githubusercontent.com/thiagomata/prime-numbers/master/charts/full-cycle-survival.svg)

A figura é gerada pelo [cálculo de sobrevivência de ciclo completo](https://github.com/thiagomata/prime-numbers/blob/master/python/src/sieve_sequence/full_cycle_survival_chart.py).

Lidas em conjunto, as duas figuras de ciclo completo dão uma progressão direta
da identidade de um filtro para seu efeito cumulativo. Um experimento separado
de coorte fixa então faz a próxima pergunta: o que permanece verdadeiro quando
uma janela finita corta ciclos parciais? Ele segue todo início de lacuna 2
inicialmente presente em $[Q,Q^2)$ através de todos os filtros $r<Q$.
Comparações exatas de conjuntos em $Q=17$ e $Q=101$ confirmam que essa coorte
explícita concorda camada a camada com a linhagem mantida da Leitura A. Para

```math
c_{\mathrm{eff}}(r)
:=\frac{\widehat D_{\mathrm{real}}(r)-D_{\mathrm{random}}(r)}{2\log r},
```

as quatro execuções $Q\in\{17,101,251,503\}$ dão valores sinalizados entre
$-0.0353$ e $0.00908$. O maior valor positivo é $0.00907$ em $Q=251$; entre as
duas execuções maiores, todos os valores absolutos são no máximo $0.00908$.
Como o excesso de ciclo completo é exatamente zero, os desvios surgem quando o
intervalo fixo corta ciclos parciais. Seu tamanho e posicionamento permanecem
fatos empíricos finitos; a localização em ciclos parciais pode conter a
dificuldade aritmética que a identidade de ciclo completo não vê.

![Risco cumulativo de coortes de lacunas 2 em janela fixa para quatro valores finitos de Q](https://raw.githubusercontent.com/thiagomata/prime-numbers/master/charts/fixed-lineage-hazard.svg)

A figura é gerada pelo [cálculo de risco de linhagem fixa](https://github.com/thiagomata/prime-numbers/blob/master/python/src/sieve_sequence/fixed_lineage_hazard_chart.py)
a partir dos CSVs dedicados de coorte fixa. Seu valor é uma checagem de
robustez: mesmo em janelas finitas não alinhadas, os desvios de fronteira são
pequenos em relação às escalas de comparação $c=1/2$ e $c=1$.

Nenhuma dessas medições segue o par distinguido na cabeça. Transferir o diagrama
de fases da cabeça ainda exige um teorema aritmético que controle o
posicionamento coerente acoplado por CRT junto com disponibilidade persistente e
dependência entre camadas.

<a id="9-limitations"></a>

## 9. Limitações

Os companheiros balanceados rastreiam descendentes de lacunas 2 existentes, em
vez de uma sequência coerente aleatorizada de inteiros. Eles não modelam lacunas
que não são 2, mesclagens de lacunas ou efeitos de extremos compartilhados. Seu
adversário é mais forte que o filtro real porque pode selecionar cópias
prejudiciais separadamente para cada pai. A política do pai protetor também é um
oráculo: ela conhece o alvo atual e move ambas as deleções para outro lugar.
Nenhum dos extremos é uma descrição do filtro real.

O teorema de janela adversarial/aleatória assume uniformidade espacial. O
teorema de janela adversarial/protetora, por sua vez, assume um suprimento
protetor quadrático $B(Q)$. Seu teorema da cabeça assume uma linhagem elegível
de pai protetor na cabeça com disponibilidade limitada inferiormente. Nenhuma
dessas premissas segue apenas da escolha de exatamente dois.

O teorema de quota CRT exata/localização aleatória preserva contagens de ataques,
mas descarta suas localizações aritméticas determinísticas. Sua conclusão de
recorrência exige as condições cumulativas de quota em [§7.1](#71-exact-crt-quotas-with-random-locations), disponibilidade persistente
na cabeça e mistura entre camadas. A fórmula local exata $A(p,q)$ não estabelece
essas premissas apenas por ser exata.

O teorema de quota enviesada assume adicionalmente uma lei de alocação trocável
por grupos e acertos duplos de ordem quadrática em um par de extremos. Seu peso
bruto $\beta_r$ não é o mesmo que o viés efetivo de destruição $\kappa_r$: a
normalização por quota exata pode mudar seu coeficiente principal para a
população elegível da peneira. Um caso bruto de igualdade deve, portanto, ser
decidido por meio de $D_{\kappa}(Q)$ e das condições de viabilidade da quota.

O uso de população esperada também tem uma fronteira estrita. Uma esperança que
tende ao infinito não prova sozinha janelas não vazias; o limite somável de
janela vazia fornece esse passo sob posicionamento uniforme. Do mesmo modo, uma
série divergente de eventos de cabeça não prova sozinha recorrência infinita;
independência ou mistura adequada entre camadas é necessária. Quotas exatas,
moedas de filtro inteiro, balanço por blocos, informação atrasada e ranqueamento
ruidoso criam dependências diferentes e não podem herdar entre si conclusões
quase certas meramente porque compartilham o mesmo orçamento marginal ou taxa de
destruição.

A comparação empírica em [§8.1](#81-finite-empirical-comparison-with-random) é finita. Dois conjuntos de dados usam uma
janela quadrada diferente em cada estágio medido; o conjunto de coorte fixa, em
vez disso, segue todos os inícios iniciais de lacunas 2 em uma janela
$[Q,Q^2)$. Este último produz um risco coerente de janela, mas seu desvio em
relação à taxa exata de ciclo completo vem da localização em ciclos parciais, e
a coorte não é o par distinguido na cabeça. Portanto, nenhum dos dados substitui
disponibilidade persistente, mistura entre camadas ou uma prova aritmética
abaixo da fronteira de cabeça $c=1/2$.

Portanto, provamos um diagrama de fases para os companheiros definidos. A
questão restante é se a peneira real ocupa um desses regimes.

<a id="10-conclusion"></a>

## 10. Conclusão

Companheiros balanceados de lacunas 2 tornam a persistência global
deliberadamente não informativa: todo pai sempre deixa $r-2$ filhos, então a
população de período completo cresce sob seleção protetora, aleatória,
adversarial e mista igualmente. A distinção local é carregada pela destruição
condicional relativa ao aleatório, seu risco cumulativo e a alocação. Dados
finitos da peneira real, em vez disso, fornecem frações observadas de coortes,
que exigem um teorema de transferência separado.

A prova começa com a recorrência global exata e então substitui a contagem de
população pelo risco local cumulativo:

```math
\begin{aligned}
N_{k+1}&=(r_k-2)N_k,\\
w_r&=\frac{rf_r}{2},\\
D(Q)&=\sum_{r < Q}-\log(1-f_r),\\
P(Q)&=e^{-D(Q)}.
\end{aligned}
```

A resposta principal é que não há fator constante finito máximo pior que o
aleatório. Se $w_r=w < \infty$, a sobrevivência local decai apenas como
$(\log Q)^{-2w}$; o suprimento quadrático de janela quadrada ainda domina, e a
série de probabilidades da cabeça ainda diverge. Sob as premissas espaciais e
de mistura declaradas, janelas quadradas são eventualmente não vazias e lacunas
2 na cabeça recorrem infinitas vezes para todo $w$ finito fixo.

A primeira fronteira não trivial ocorre quando a piora cresce com o filtro. Sob
as condições cumulativas de quota/erro de [§7.1](#71-exact-crt-quotas-with-random-locations) e as premissas espaciais
relevantes, o companheiro neutro de quota exata recupera a escala de
sobrevivência aleatória. O companheiro de quota exata enviesada recupera as
seguintes fronteiras gerais de risco quando seu viés efetivo condicional segue
a programação exibida e suas premissas de posicionamento, disponibilidade e
mistura valem:

```math
\begin{aligned}
w_r=1+c\log r,\quad c < 1
&\Longrightarrow
\text{ocupação eventual de janela quadrada},\\
w_r=1+c\log r,\quad c < \frac12
&\Longrightarrow
\text{lacunas 2 na cabeça recorrendo infinitamente, com mistura}.
\end{aligned}
```

O teorema de alocação explica por que uma porcentagem sozinha não pode localizar
um processo neste diagrama de fases. Alocação uniforme, protetora e direcionada
podem aplicar o mesmo orçamento adversarial e produzir dano local diferente. A
quantidade que entra no teorema é, portanto, o risco local condicional, não o
rótulo de política por si só.

A comparação de período completo é exata: todo novo filtro destrói a fração
$2/r$ das lacunas 2 cíclicas expandidas, então seu excesso cumulativo sobre o
benchmark neutro é zero. Os dois diagramas de ciclo completo expõem as duas
partes dessa afirmação separadamente. O diagrama de destruição torna imediata a
identidade por filtro; o diagrama de sobrevivência mostra o que a composição
dessa identidade faz e quão fortemente ela se separa da programação $c=1$.
Nenhum diagrama é enfraquecido por ser uma renderização direta do cálculo: seu
valor é que a igualdade local e a consequência cumulativa podem ser checadas
visualmente, cada uma na representação mais adequada a ela.

As medições finitas de janela quadrada então descrevem a questão restante de
localização. Até a cabeça $1129$, a população observada tem razão média $0.967$
em relação à esperança aleatória, e as taxas medidas de janela em um passo até o
filtro $19{,}429$ estão em ou abaixo de $2/r$. Coortes fixas para
$Q=17,101,251,503$ têm coeficientes efetivos sinalizados entre $-0.0353$ e
$0.00908$; essas são medições finitas de ciclos parciais em torno da lei exata
de ciclo. As medições permanecem longe da escala de falha de janela $c=1$, mas
não localizam o par distinguido na cabeça em relação à fronteira de recorrência
$c=1/2$.

A pergunta sobre a peneira real agora é expressável como uma comparação
cumulativa, em vez de uma afirmação vaga de comportamento aleatório ou
adversarial: medir a destruição observada da coorte $\widehat f_r$ gerada pelos
índices prejudiciais acoplados por CRT, normalizá-la para $\widehat w_r$ e
estabelecer se essas observações controlam os riscos candidatos relevantes e o
posicionamento perto da cabeça.

Aqui está um critério determinístico explícito suficiente de contagem. Seja
$I_Q\in\{0,1\}$ indicando que a peneira real tem uma lacuna 2 na cabeça prima
$Q$. Seja $\rho_Q>0$ o peso de referência companheiro obtido a partir do risco
cumulativo abaixo da fronteira e do limite de disponibilidade declarado, e
defina

```math
R(X):=\sum_{\substack{Q\le X\\Q\text{ prime}}}\rho_Q.
```

Assuma

```math
\begin{aligned}
R(X)&\longrightarrow\infty,
&&[\text{Massa de Referência Divergente}]\\
\sum_{\substack{Q\le X\\Q\text{ prime}}}(I_Q-\rho_Q)
&=o(R(X)).
&&[\text{Limite Determinístico de Discrepância}]
\end{aligned}
```

Então

```math
\sum_{\substack{Q\le X\\Q\text{ prime}}}I_Q
=R(X)+o(R(X))
\longrightarrow\infty.
\qquad[\text{C.Q.D.}]
```

Esta é uma condição suficiente não provada para a peneira CRT real. Ela é mais
forte que a própria recorrência porque afirma uma fórmula assintótica de
contagem. A massa de referência precisa divergir, em vez de todo filtro
individual satisfazer um limite pontual. “Infinitas vezes” não significa que
toda cabeça suficientemente grande seja uma lacuna 2. Provar essa condição
provaria infinitas lacunas 2 na cabeça e, portanto, a conjectura dos primos
gêmeos; ela não segue das estimativas de risco deste artigo.

<a id="11-future-work"></a>

## 11. Trabalho Futuro

Os teoremas companheiros reduzem a pergunta sobre a peneira real a entradas
aritméticas mensuráveis. A primeira direção é estimar o risco local real
$D_{\kappa}(Q)$ a partir de localizações de filtros acopladas por CRT e compará-lo
com a fronteira da cabeça sem atribuir intenção hostil a filtros individuais. A
segunda é substituir a premissa estocástica de mistura por um teorema
determinístico de descorrelação ou discrepância forte o suficiente para
transferir uma soma divergente de eventos de cabeça para a sequência real. A
terceira é testar companheiros de quota exata, atrasados, balanceados por blocos
e com ranqueamento ruidoso nas mesmas transições, reportando tanto a preferência
bruta por extremos quanto o viés efetivo normalizado por quota.

Essas direções são deliberadamente separadas. Um experimento finito pode
identificar qual companheiro se parece com a peneira observada, mas não pode
estabelecer o teorema infinito de transferência. Reciprocamente, um teorema de
discrepância precisa controlar onde os ataques CRT reais pousam, não apenas
quantos ataques ou lacunas 2 globais existem.

<a id="12-references"></a>

## 12. Referências

<a name="ref1" id="ref1" href="#ref1">[1]</a>
Mata, T. H. (2026). *Formal Verification of Sieve Sequence Stages and Their
Transitions*. Disponível em: [https://doi.org/10.5281/zenodo.22955782](https://doi.org/10.5281/zenodo.22955782).

<a name="ref2" id="ref2" href="#ref2">[2]</a>
Mata, T. H. (2026). *Structural Properties and Signed Boundaries of 2-Gaps in
Sieve Sequences*. Disponível em: [https://doi.org/10.5281/zenodo.22955786](https://doi.org/10.5281/zenodo.22955786).

<a name="ref3" id="ref3" href="#ref3">[3]</a>
Kochen, S. e Stone, C. (1964). [A note on the Borel--Cantelli lemma](
https://doi.org/10.1215/ijm/1256059668). *Illinois Journal of Mathematics*,
8(2), 248--251.

<a name="ref4" id="ref4" href="#ref4">[4]</a>
Hardy, G. H. e Wright, E. M.; revisado por Heath-Brown, D. R. e Silverman,
J. H. (2008). [*An Introduction to the Theory of Numbers*](
https://doi.org/10.1093/oso/9780199219858.001.0001), 6th edition. Oxford
University Press.

## Apêndice A. Registros Selecionados de Provas Companheiras

O corpo desenvolve todo resultado em seu contexto matemático. Este apêndice
reúne seis registros centrais de provas de processos companheiros com suas
premissas e conclusões; é uma referência selecionada, não um catálogo completo
do corpo.

<a id="appendix-a1"></a>

### A.1 A Persistência Global é Independente da Alocação

Uma vez que a população inicial é não nula, este resultado é incondicional em
relação à alocação dentro de todo companheiro balanceado. Seja
$N_k=|\mathcal G_k|$ a população de lacunas 2 em período completo antes de
instalar o primo $r_k$, com $N_0>0$. Todo pai produz $r_k$ cópias e perde
exatamente duas, independentemente de onde essas duas remoções ocorrem. Portanto

```math
\begin{aligned}
N_{k+1}
&=\sum_{g\in\mathcal G_k}(r_k-2)
&&[\text{Exatamente Duas Cópias Removidas por Pai}]\\
&=(r_k-2)N_k.
&&[\text{Simplificação}]
\end{aligned}
```

Iterar a recorrência dá

```math
\begin{aligned}
N_k
&=N_0\prod_{i < k}(r_i-2)
&&[\text{Iteração}]\\
&>0
&&[N_0>0;\ r_i\ge5]\\
&\longrightarrow\infty.
&&[\text{Todo Fator é Pelo Menos }3]
\end{aligned}
\qquad[\text{C.Q.D.}]
```

Assim, a alocação pode eliminar lacunas 2 da cabeça ou de uma janela rastreada,
mas não pode esgotar a população de período completo enquanto a regra de remoção
de exatamente duas é preservada.

<a id="appendix-a2"></a>

### A.2 Lei Cumulativa de Risco Local

Acompanhe um candidato inicialmente elegível através de filtros sucessivos. Seja
$f_r$ sua probabilidade condicional de destruição, dada a sobrevivência anterior
e a elegibilidade inicial, e assuma $0\le f_r < 1$. Defina

```math
w_r:=\frac{rf_r}{2},
\qquad
D(Q):=\sum_{r < Q}-\log(1-f_r).
```

Os fatores condicionais de sobrevivência se multiplicam pela regra da cadeia de
probabilidade, sem exigir eventos de filtro independentes:

```math
\begin{aligned}
P(Q)
&=\prod_{r < Q}(1-f_r)
&&[\text{Sobrevive a Todo Filtro}]\\
&=\exp\left(\sum_{r < Q}\log(1-f_r)\right)
&&[\text{Produto para Soma}]\\
&=e^{-D(Q)}.
&&[\text{Definição de }D(Q)]
\end{aligned}
\qquad[\text{C.Q.D.}]
```

Para o benchmark aleatório $w_r=1$, a soma harmônica dos primos dá

```math
\begin{aligned}
D_{\mathrm{random}}(Q)
&=\sum_{r < Q}-\log\left(1-\frac2r\right)\\
&=2\log\log Q+O(1),\\
P_{\mathrm{random}}(Q)
&\asymp\frac{C}{(\log Q)^2}.
\end{aligned}
```

Essa identidade determina a probabilidade de sobrevivência do candidato a partir
de seus riscos condicionais. Para uma coorte finita aninhada fixa, o produto
análogo de frações observadas dá sua razão entre tamanho final e inicial.
Nenhuma versão fornece abundância de janela, disponibilidade na cabeça ou
mistura entre camadas. Um passo letal elimina o candidato ou a coorte
rastreada, não todo candidato posterior.

<a id="appendix-a3"></a>

### A.3 Todo Fator Fixo Finito de Piora Sobrevive

Seja $w\ge0$ fixo e suponha $f_r=2w/r$ para todos os filtros suficientemente
grandes. Um prefixo finito muda apenas a constante principal positiva. Como o
resto quadrático de Taylor é somável sobre primos, o Apêndice A.2 dá

```math
\begin{aligned}
D_w(Q)
&=\sum_{r < Q}-\log\left(1-\frac{2w}{r}\right)
&&[\text{Definição de }D(Q)]\\
&=2w\sum_{r < Q}\frac1r+O(1)
&&[\text{Expansão de Taylor; Resto Somável}]\\
&=2w\log\log Q+O(1).
&&[\text{Soma Harmônica dos Primos}]
\end{aligned}
```

Portanto

```math
P_w(Q)\asymp\frac{C_w}{(\log Q)^{2w}}.
```

Assuma primeiro que uma janela quadrada fornece $B(Q)\asymp C_0Q^2$ linhagens
elegíveis e que seu posicionamento satisfaz o limite cego de janela vazia. Sua
população sobrevivente esperada é

```math
\lambda_w(Q)
\asymp
C_0\frac{Q^2}{(\log Q)^{2w}}
\longrightarrow\infty.
```

Esse crescimento polinomial torna somáveis as probabilidades de janela vazia,
então apenas finitas janelas quadradas são vazias quase certamente. Para uma
cabeça distinguida cuja disponibilidade de base é limitada inferiormente,

```math
\Pr(H_Q)\asymp\frac{C_w}{(\log Q)^{2w}}.
```

A soma sobre cabeças primas diverge para todo $w$ finito. Com mistura adequada
entre camadas, lacunas 2 na cabeça, portanto, recorrem infinitas vezes quase
certamente. Logo, não há máximo finito de fator constante pior que o aleatório.
$\blacksquare$

<a id="appendix-a4"></a>

### A.4 Piora Logaritmicamente Crescente Tem Dois Limiares

Mantenha as premissas de suprimento, disponibilidade, posicionamento e mistura
do Apêndice A.3, e defina

```math
w_r=1+c\log r,
\qquad c\ge0.
```

Então $f_r=2/r+2c\log r/r$. A soma sobre primos e o resto somável de Taylor dão

```math
\begin{aligned}
D_c(Q)
&=\sum_{r < Q}-\log(1-f_r)
&&[\text{Definição de }D(Q)]\\
&=2\sum_{r < Q}\frac1r
+2c\sum_{r < Q}\frac{\log r}{r}+O(1)
&&[\text{Substituição; Resto Somável}]\\
&=2\log\log Q+2c\log Q+O(1).
&&[\text{Assintótica de Soma sobre Primos}]
\end{aligned}
```

Consequentemente,

```math
P_c(Q)
\asymp
\frac{C_c}{Q^{2c}(\log Q)^2}.
```

Para um suprimento quadrático de janela quadrada,

```math
\lambda_c(Q)
\asymp
C_0\frac{Q^{2-2c}}{(\log Q)^2}.
```

Assim, $c < 1$ dá ocupação eventual de janela quadrada quase certamente sob a
premissa de posicionamento cego, enquanto $c\ge1$ faz a população esperada
tender a zero. Para a cabeça, a série de ocorrência prima tem o mesmo
comportamento de convergência que

```math
\int^\infty\frac{dx}{x^{2c}(\log x)^3}.
```

A integral diverge para $c < 1/2$ e converge para $c\ge1/2$. Portanto

```math
\begin{aligned}
c < 1
&\Longrightarrow
\text{ocupação eventual de janela quadrada quase certamente},\\
c < \frac12
&\Longrightarrow
\text{lacunas 2 na cabeça recorrendo infinitamente quase certamente, com mistura}.
\end{aligned}
\qquad[\text{C.Q.D.}]
```

O intervalo intermediário $1/2\le c < 1$ preserva janelas quadradas, mas não
eventos de cabeça recorrendo infinitamente. Programações irregulares precisam
ser avaliadas pelo risco cumulativo $D(Q)$, em vez de por valores pontuais
isolados.

<a id="appendix-a5"></a>

### A.5 Fronteira de Janela Quadrada Adversarial/Aleatória

No filtro $r$, seja um pai adversarial com parcela $\alpha_r$ e aleatório caso
contrário. Para uma linhagem localmente relevante,

```math
1-f_r
=(1-\alpha_r)\left(1-\frac2r\right).
```

Defina o risco cumulativo da parcela adversarial

```math
A(Q):=\sum_{r < Q}-\log(1-\alpha_r).
```

A densidade de sobrevivência aleatória contribui $(\log Q)^{-2}$, enquanto a
parcela adversarial repetida contribui $e^{-A(Q)}$. Se a janela segura pelo
quadrado tem comprimento $L_Q\asymp Q^2$ e os inícios sobreviventes obedecem ao
modelo de uniformidade espacial, então

```math
\begin{aligned}
\lambda_Q^{\mathrm{mix}}
&=L_Q\delta_Q^{\mathrm{mix}}
&&[\text{Ocupação Uniforme Esperada}]\\
&\asymp
C\frac{Q^2}{(\log Q)^2}e^{-A(Q)}.
&&[\text{Sobrevivência Cumulativa}]
\end{aligned}
```

Tomar logaritmos dá

```math
\log\lambda_Q^{\mathrm{mix}}
=2\log Q-2\log\log Q-A(Q)+O(1).
```

Portanto, para todo $\varepsilon>0$ fixo,

```math
\begin{aligned}
A(Q)\le(2-\varepsilon)\log Q
&\Longrightarrow
\lambda_Q^{\mathrm{mix}}\longrightarrow\infty,
&&[\text{Orçamento Subcrítico}]\\
A(Q)\ge(2+\varepsilon)\log Q
&\Longrightarrow
\lambda_Q^{\mathrm{mix}}\longrightarrow0.
&&[\text{Orçamento Supercrítico}]
\end{aligned}
```

Na fronteira exata, o termo $-2\log\log Q$ precisa ser retido. Sob
posicionamento uniforme,

```math
\Pr(X_Q=0)\le e^{-\lambda_Q^{\mathrm{mix}}}.
```

Logo, a condição de somabilidade

```math
\sum_{Q\text{ prime}}e^{-\lambda_Q^{\mathrm{mix}}}<\infty
```

implica que apenas finitas janelas quadradas são vazias quase certamente. Uma
condição suficiente conveniente é
$\lambda_Q^{\mathrm{mix}}\ge(1+\varepsilon)\log Q$ para todo $Q$ suficientemente
grande. $\blacksquare$

<a id="appendix-a6"></a>

### A.6 Intervalo de Alocação de Sobreviventes Locais

Considere uma janela alvo menor que o período antigo, de modo que cada pai
contribui no máximo um filho-alvo. Seja $N$ o número de pais, seja $R$ o
conjunto dos $L$ pais relevantes, e seja $\mathcal A$ o conjunto de tamanho $K$
que recebe tratamento adversarial. Todo pai fora de $\mathcal A$ é protetor e
preserva seu filho-alvo. O número de filhos-alvo destruídos e sobreviventes é

```math
H=|\mathcal A\cap R|,
\qquad
S=L-H.
```

A interseção não pode exceder nenhum dos conjuntos, e no máximo $N-L$ rótulos
adversariais podem ser colocados fora de $R$. Logo

```math
\begin{aligned}
H
&\le\min(K,L),
&&[\text{Limite Superior da Interseção}]\\
H
&\ge\max(0,K-(N-L)).
&&[\text{Capacidade dos Pais Irrelevantes}]
\end{aligned}
```

Substituição em $S=L-H$ dá o intervalo agudo de sobreviventes

```math
\max(0,L-K)
\le S\le
\min(L,N-K).
```

Ambos os extremos são atingíveis. Um alocador ciente do alvo seleciona pais
relevantes primeiro, enquanto um alocador protetor atribui os rótulos
adversariais a pais irrelevantes primeiro:

```math
\begin{aligned}
S_{\mathrm{targeted}}&=\max(0,L-K),\\
S_{\mathrm{protective}}&=\min(L,N-K).
\end{aligned}
```

Se $\mathcal A$ é, em vez disso, um subconjunto uniformemente aleatório de
tamanho $K$, então

```math
H\sim\text{Hypergeometric}(N,L,K),
```

então

```math
\begin{aligned}
\mathbb E[H]&=\frac{KL}{N},\\
\mathbb E[S]&=L\left(1-\frac KN\right).
\end{aligned}
```

Quando $K\ge L$, a alocação uniforme limpa o alvo com probabilidade

```math
\Pr(S=0)
=\frac{\binom{N-L}{K-L}}{\binom NK}
=\frac{\binom KL}{\binom NL}.
```

Escrevendo $\alpha=K/N$, o extremo direcionado se torna

```math
S_{\mathrm{targeted}}=0
\Longleftrightarrow
K\ge L
\Longleftrightarrow
\alpha\ge\frac LN.
\qquad[\text{C.Q.D.}]
```

Na cabeça, $L=1$, então um rótulo adversarial corretamente colocado destrói o
candidato atual. Se $L/N\longrightarrow0$ em uma janela rastreada, todo
$\alpha>0$ fixo eventualmente tem capacidade suficiente para limpar essa
janela. O Apêndice A.1 ainda se aplica: os pais direcionados deixam $r-2$
descendentes fora da janela, então o crescimento de período completo continua.
