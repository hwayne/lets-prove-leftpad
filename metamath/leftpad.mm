$( Include the "set.mm", the main ZFC database $)
$[ set.mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  LeftPad
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Define the ` leftpad ` constant. $)
  $c leftpad $.

  $( Extend class notation with the ` leftpad ` function. $)
  clpad $a class leftpad $.

  ${
    $d c l w $.
    $( Define the ` leftpad ` function.  (Contributed by Thierry Arnoux,
       7-Aug-2023.) $)
    df-lpad $a |- leftpad = ( c e. _V , w e. _V |-> ( l e. NN0 |->
        ( ( ( 0 ..^ ( l - ( # ` w ) ) ) X. { c } ) ++ w ) ) ) $.
  $}

  ${
    $d C c l w $.  $d L l $.  $d W c l w $.  $d c l ph w $.
    lpadval.1 $e |- ( ph -> L e. NN0 ) $.
    lpadval.2 $e |- ( ph -> W e. Word S ) $.
    lpadval.3 $e |- ( ph -> C e. S ) $.
    $( Value of the ` leftpad ` function.  (Contributed by Thierry Arnoux,
       7-Aug-2023.) $)
    lpadval $p |- ( ph -> ( ( C leftpad W ) ` L ) = ( ( ( 0 ..^ ( L - ( # ` W )
       ) ) X. { C } ) ++ W ) ) $=
      ( vl vc vw cc0 cv cmin co cfzo cconcat cn0 cvv wceq chash cfv clpad cmpt2
      csn cxp cmpt df-lpad wa simprr fveq2d oveq2d simprl sneqd xpeq12d oveq12d
      mpteq2dv elexd cword wcel nn0ex mptexd ovmpt2d simpr oveq1d xpeq1d fvmptd
      a1i ovexd ) AIDLIMZEUAUBZNOZPOZBUEZUFZEQOZLDVKNOZPOZVNUFZEQORBEUCOSAJKBES
      SIRLVJKMZUAUBZNOZPOZJMZUEZUFZVTQOZUGZIRVPUGUCSUCJKSSWHUDTAKJIUHVHAWDBTZVT
      ETZUIUIZIRWGVPWKWFVOVTEQWKWCVMWEVNWKWBVLLPWKWAVKVJNWKVTEUAAWIWJUJUKULULWK
      WDBAWIWJUMUNUOAWIWJUJUPUQABCHURAECUSGURAIRVPSRSUTAVAVHVBVCAVJDTZUIZVOVSEQ
      WMVMVRVNWMVLVQLPWMVJDVKNAWLVDVEULVFVEFAVSEQVIVG $.
  $}

  ${
    lpadlem1.1 $e |- ( ph -> C e. S ) $.
    $( Lemma for the ` leftpad ` theorems.  (Contributed by Thierry Arnoux,
       7-Aug-2023.) $)
    lpadlem1 $p |- ( ph -> ( ( 0 ..^ ( L - ( # ` W ) ) ) X. { C } ) e. Word S )
       $=
      ( wcel cc0 chash cfv cmin co cfzo csn cxp wf cword fconst6g iswrdi 3syl )
      ABCGHDEIJKLZMLZCUBBNOZPUCCQGFUBBCRCUAUCST $.
  $}

  ${
    lpadlen.1 $e |- ( ph -> L e. NN0 ) $.
    lpadlen.2 $e |- ( ph -> W e. Word S ) $.
    lpadlen.3 $e |- ( ph -> C e. S ) $.
    ${
      lpadlen1.1 $e |- ( ph -> L <_ ( # ` W ) ) $.
      $( Lemma for ~ lpadlen1 (Contributed by Thierry Arnoux, 7-Aug-2023.) $)
      lpadlem3 $p |- ( ph -> ( ( 0 ..^ ( L - ( # ` W ) ) ) X. { C } ) = (/) )
        $=
        ( cc0 chash cfv cmin co cfzo cxp c0 cz wcel nn0zd csn cle wbr cword cn0
        wceq lencl syl wa fzo0n biimpa syl21anc xpeq1d 0xp syl6eq ) AJDEKLZMNON
        ZBUAZPQURPQAUQQURAUPRSZDRSZDUPUBUCZUQQUFZAUPAECUDSUPUESGCEUGUHTADFTIUSU
        TUIVAVBUPDUJUKULUMURUNUO $.

      $( Length of a left-padded word, in the case the given word ` W ` is
         shorter than the desired length.  (Contributed by Thierry Arnoux,
         7-Aug-2023.) $)
      lpadlen1 $p |- ( ph -> ( # ` ( ( C leftpad W ) ` L ) ) = ( # ` W ) ) $=
        ( clpad co cfv chash cc0 cmin cfzo csn cxp cconcat c0 oveq1d cword wcel
        lpadval lpadlem3 wceq ccatlid syl 3eqtrd fveq2d ) ADBEJKLZEMAUKNDEMLOKP
        KBQRZESKTESKZEABCDEFGHUDAULTESABCDEFGHIUEUAAECUBUCUMEUFGCEUGUHUIUJ $.
    $}

    ${
      lpadlen2.1 $e |- ( ph -> ( # ` W ) <_ L ) $.
      $( Lemma for the ` leftpad ` theorems.  (Contributed by Thierry Arnoux,
         7-Aug-2023.) $)
      lpadlem2 $p |- ( ph -> ( # ` ( ( 0 ..^ ( L - ( # ` W ) ) ) X. { C } ) )
          = ( L - ( # ` W ) ) ) $=
        ( cc0 chash cfv co cmul c1 wceq cfn wcel cn0 syl cmin cfzo csn cxp snfi
        fzofi hashxp mp2an a1i cle cword lencl nn0sub2 syl3anc hashfzo0 hashsng
        wbr oveq12d nn0cnd mulid1d 3eqtrd ) AJDEKLZUAMZUBMZBUCZUDKLZVDKLZVEKLZN
        MZVCONMVCVFVIPZAVDQRVEQRVJJVCUFBUEVDVEUGUHUIAVGVCVHONAVCSRZVGVCPAVBSRZD
        SRZVBDUJUQZVKAECUKRZVLGCEULTFIVBDUMUNVCUOTABCRVHOPHBCUPTURAVCAVCAVLVMVN
        VKAVOVLGCEULTFIVBDUMUNUSUTVA $.

      $( Length of a left-padded word, in the case the given word ` W ` is
         shorter than the desired length.  (Contributed by Thierry Arnoux,
         7-Aug-2023.) $)
      lpadlen2 $p |- ( ph -> ( # ` ( ( C leftpad W ) ` L ) ) = L ) $=
        ( clpad co cfv chash cc0 cmin cfzo csn caddc wcel nn0cnd cconcat fveq2d
        cxp lpadval cword wceq lpadlem1 ccatlen syl2anc lpadlem2 oveq1d cn0 syl
        lencl npcand 3eqtrd eqtrd ) ADBEJKLZMLNDEMLZOKZPKBQUCZEUAKZMLZDAURVBMAB
        CDEFGHUDUBAVCVAMLZUSRKZUTUSRKDAVACUEZSEVFSZVCVEUFABCDEHUGGCVAEUHUIAVDUT
        USRABCDEFGHIUJUKADUSADFTAUSAVGUSULSGCEUNUMTUOUPUQ $.
    $}

    $( Length of a left-padded word, in the general case, expressed with an
       ` if ` statement.  (Contributed by Thierry Arnoux, 7-Aug-2023.) $)
    lpadmax $p |- ( ph -> ( # ` ( ( C leftpad W ) ` L ) )
       = if ( L <_ ( # ` W ) , ( # ` W ) , L ) ) $=
      ( chash cfv wbr wceq eqeq2 wa cn0 wcel adantr lencl syl nn0red cle co cif
      clpad cword simpr lpadlen1 wn clt ltnled biimpar ltled lpadlen2 ifbothda
      cr ) DEIJZUAKZDBEUDUBJIJZUPLURDLURUQUPDUCZLAUPDUPUSURMDUSURMAUQNBCDEADOPZ
      UQFQAECUEPZUQGQABCPZUQHQAUQUFUGAUQUHZNZBCDEAUTVCFQAVAVCGQAVBVCHQVDUPDAUPU
      OPVCAUPAVAUPOPZGCERSTQVDDAUTVCFQTAUPDUIKVCAUPDAUPAVAVEGCERSTADFTUJUKULUMU
      N $.

    ${
      lpadleft.1 $e |- ( ph -> N e. ( 0 ..^ ( L - ( # ` W ) ) ) ) $.
      $( The contents of prefix of a left-padded word is always the letter
         ` C ` .  (Contributed by Thierry Arnoux, 7-Aug-2023.) $)
      lpadleft $p |- ( ph -> ( ( ( C leftpad W ) ` L ) ` N ) = C ) $=
        ( clpad co cfv cc0 chash cfzo wcel wceq cn0 wbr csn cxp cconcat lpadval
        cmin fveq1d cword lpadlem1 cle lencl syl cn clt w3a elfzo0 sylib simp2d
        nnnn0d wa biimpar syl21anc lpadlem2 eleqtrrd ccatval1 syl3anc fvconst2g
        nn0sub oveq2d syl2anc 3eqtrd ) AEDBFKLMZMENDFOMZUELZPLZBUAUBZFUCLZMZEVO
        MZBAEVKVPABCDFGHIUDUFAVOCUGZQFVSQZENVOOMZPLZQVQVRRABCDFIUHHAEVNWBJAWAVM
        NPABCDFGHIAVLSQZDSQZVMSQZVLDUITZAVTWCHCFUJUKGAVMAESQZVMULQZEVMUMTZAEVNQ
        ZWGWHWIUNJEVMUOUPUQURWCWDUSWFWEVLDVGUTVAVBVHVCCVOFEVDVEABCQWJVRBRIJVNBE
        CVFVIVJ $.
    $}

    ${
      lpadright.1 $e |- ( ph -> M = if ( L <_ ( # ` W ) , 0 , ( L - ( # ` W ) )
        ) ) $.
      lpadright.2 $e |- ( ph -> N e. ( 0 ..^ ( # ` W ) ) ) $.
      $( The suffix of a left-padded word the original word ` W ` .
         (Contributed by Thierry Arnoux, 7-Aug-2023.) $)
      lpadright $p |- ( ph
          -> ( ( ( C leftpad W ) ` L ) ` ( N + M ) ) = ( W ` N ) ) $=
        ( co cfv cc0 chash wceq wcel adantr nn0red caddc clpad cmin csn cconcat
        cfzo cxp lpadval fveq1d cle wbr eqeq2 wa c0 cword simpr lpadlem3 fveq2d
        cif cn0 hash0 syl6eq wn cr lencl syl clt ltnled ltled lpadlem2 ifbothda
        biimpar eqtr4d oveq2d lpadlem1 ccatval3 syl3anc 3eqtr2d ) AFEUAMZDBGUBM
        NZNVSODGPNZUCMZUFMBUDUGZGUEMZNFWCPNZUAMZWDNZFGNZAVSVTWDABCDGHIJUHUIAWFV
        SWDAWEEFUAAWEDWAUJUKZOWBUSZEWIWEOQWEWBQWEWJQAOWBOWJWEULWBWJWEULAWIUMZWE
        UNPNOWKWCUNPWKBCDGADUTRZWIHSAGCUOZRZWIISABCRZWIJSAWIUPUQURVAVBAWIVCZUMZ
        BCDGAWLWPHSAWNWPISAWOWPJSWQWADAWAVDRWPAWAAWNWAUTRZICGVEVFTSADVDRWPADHTS
        AWADVGUKWPAWADAWAAWNWRICGVEVFTADHTVHVLVIVJVKKVMVNURAWCWMRWNFOWAUFMRWGWH
        QABCDGJVOILCWCGFVPVQVR $.
    $}
  $}
