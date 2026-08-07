# evm.asm: Lean 4でzkEVMを構築するための検証済みマクロアセンブラ（初期実験版）

<!-- hy-mt2-i18n:start -->
[Español](./README.md) | [中文](./README_zh-CN.md) | [English](./README_en.md) | **日本語**
<!-- hy-mt2-i18n:end -->


zkEVMを対象とした検証済みマクロアセンブラのプロトタイプ実装で、RISC-V RV64IMバックエンドを基盤としており、以下の論文に着想を得ています：

> Andrew Kennedy, Nick Benton, Jonas B. Jensen, Pierre-Evariste Dagand.
> **「Coq：世界最高のマクロアセンブラか？」**
> *第15回宣言的プログラミングの原理と実践に関する国際シンポジウム（PPDP 2013）論文集*、2013年9月、ACM。
> https://www.microsoft.com/en-us/research/publication/coq-worlds-best-macro-assembler/

## 警告：これは実験用プロトタイプのみです

**本プロジェクトは、いかなる実用的な目的にも使用してはいけません。**

これは重大な制限を持つ実験的な研究プロトタイプです：

- **RISC-V仕様への準拠なし**：命令の意味論はvibeによって生成されており、公式のRISC-V仕様に基づいて検証されていません。実際のRISC-Vの動作とは微妙な（あるいはそれほど微妙でない）違いが生じている可能性があります。
- **EVM仕様への準拠なし**：例示用の仕様もvibeによって生成されたものであり、EVM仕様に基づいて検証されていません。
- **適合性テストの欠如**：この実装が実際のRISC-Vプロセッサやシミュレータと一致しているかを確認するための体系的なテストは行われていません。EVMに関するテストも実施されていません。
- **プロトタイプとしての品質**：このコードは検証済みマクロアセンブリ技術を探求するための教育・研究目的でのものであり、実運用向けではありません。

## 効果：zkEVMにおけるコンパイラへの信頼を排除する

zkVMを利用する通常の方法は、高水準なプログラムをRISC-Vアセンブリにコンパイルし、その後ゼロ知識証明システムを用いて実行トレースの正しさを証明することです。この証明は*実行トレース*を対象としますが、*コンパイラ*自体まではカバーできません。もしコンパイラにバグや悪意がある場合、ZK証明が有効であり、ソースコード自体も正しいにもかかわらず、証明結果が開発者（または受取人）の意図と一致しない可能性があります。

**evm.asm**は別のアプローチを探求している。すなわち、プログラムを直接RISC-Vコードとして記述し、ZK証明が生成される前にLean 4を用いてその正しさを*証明*するのである。これにより、開発者（またはZK証明の受取人）はゲストプログラムに関してコンパイラを信頼する必要が全くなくなるのだ。

より具体的に言えば、evm.asmは**zkEVM**のゲスト部分を構築することを目指している。この利用形態においては、信頼できるコンピューティング基盤を縮小することが重要だ。

### L1-zkEVMスタックにおける役割

目指す形態とは、L1 zkVMプローバーが利用可能な**ステートレスなブロックバリデーターELF**であり、これは現在[`eth-act/ere-guests`](https://github.com/eth-act/ere-guests)にあるRustでコンパイルされた`stateless-validator-{reth,ethrex}`バイナリが占めているのと同じ役割を担うものです。evm.asmも[`eth-act/zkvm-standards`](https://github.com/eth-act/zkvm-standards)のIOインターフェースに従い、入力が`(block, execution_witness)`、出力がポストステートのルートという同じ形式を目指していますが、高水準なELクライアントではなく検証済みのRV64コアから下位層から構築されるため、生成されるアーティファクトにはRLP-bytes-inからstate-root-outまでのLeanカーネルによってチェックされたHoareトリプルが含まれ、TCB内にはコンパイラが存在しません。このようなゲストプログラムのベンチマークは[`eth-act/zkevm-benchmark-workload`](https://github.com/eth-act/zkevm-benchmark-workload)および[L1 zkEVMベンチマーキングブログ](https://zkevm.ethereum.foundation/blog/benchmarking-zkvms)に掲載されています。

実行層クライアントとの連携は今後の課題です。ゲストプログラムのチェックリスト（9項目）や多次元のステータスダッシュボードについては、
[`PROGRESS.md`](PROGRESS.md) をご覧ください。

もう一つの動機として、私たちのホアー三重項はステップ数において*制限付き*であることです（`cpsTripleWithin N base...`）：すべての仕様には、プログラムが実行するRISC-Vステップ数に関する明示的な上限値`N`が設定されています。これにより2つの結果が生じます：

# 厳格な制約
1. **zkVMのサイクル制限**：`N`とは、最悪のケースにおけるサイクル予算であり、複合されたマクロ全体で合計可能で、プログラムを実行しなくてもzkVMの各証明あたりの容量制限内に収まる値です。
2. **ガスコスト**：`N`とは、検証済みの各命令コードごとの指令数であり、適切なガス価格モデルを構築するための主要な入力値です。

## 核心思想

Lean 4は同時に以下の役割を果たします：

# 厳格な制約
1. **構造の維持**：元のMarkdownデータ構造、インデント、見出し階層、表、リンク、URL、バッジ、コードブロック、インラインコードを一切変更しないこと。
2. **選択的翻訳**：ユーザーに表示される可視的な自然言語内容のみを翻訳すること。
3. **変更禁止**：コードタグ、キー名、変数プレースホルダー（{{var}}、${var}、%s、%dなど）、コマンド例、ファイルパス、プロジェクト名、API名、パッケージ名、モデル名、識別子、コード記号を翻訳したり変更したりすることは**厳禁**である。背景情報に対応する訳名が既に示されている場合を除く。
4. 用語、文体、固有名詞の翻訳は、与えられた背景情報と一致させること。

## 例：検証済みEVMオペコードの姿

各EVMオペコードは、4×64ビットからなる構成要素を操作する一連のRISC-V命令として実装されている。**スタックレベルの仕様**では、`evmWordIs`という断言を用いて、この低レベルな実装を256ビット版EVMの意味論に結びつけており、この断言とは、連続する4つのメモリワードが1つの`EvmWord`（すなわち`BitVec 256`）を表現するというものである。

```lean
-- EvmWordは連続するアドレス上にある64ビットの4つの構成要素として格納される
def evmWordIs (addr : Addr) (v : EvmWord) : Assertion :=
  (addr ↦ₘ v.getLimb 0) ** ((addr + 8) ↦ₘ v.getLimb 1) **
  ((addr + 16) ↦ₘ v.getLimb 2) ** ((addr + 24) ↦ₘ v.getLimb 3)
```

これが256ビットAND命令のスタックレベル仕様です（`EvmAsm/Evm64/And/Spec.lean`）。その内容は、スタック上にある2つの`EvmWord`である`a`と`b`から出発し、17命令からなるRISC-Vプログラム`evm_and_code`が機械によって検証された証明を伴って`a &&& b`を生成する、というものです。

```lean
/-- スタックレベルの256ビットEVM AND演算：evmWordIsを用いて2つのEvmWordに対して演算を行う。 -/
theorem evm_and_stack_spec (sp base : Addr)
    (a b : EvmWord) (v7 v6 : Word)
    (hvalid : ValidMemRange sp 8) :
    let code := evm_and_code base
    cpsTripleWithin 17 base (base + 68) code
      (-- 前提条件：スタックポインタ、一時レジスタ、2つの256ビットワード
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       evmWordIs sp a ** evmWordIs (sp + 32) b)
      (-- 後件条件：スタックポインタが進み、結果がa &&& bとなる
       (.x12 ↦ᵣ (sp + 32)) ** (.x7 ↦ᵣ (a.getLimb 3 &&& b.getLimb 3)) **
       (.x6 ↦ᵣ b.getLimb 3) **
       evmWordIs sp a ** evmWordIs (sp + 32) (a &&& b))
```

この命題は、分離論理のアサーションを含む境界付きHoareトリプル（`cpsTripleWithin`）である。前提条件では実行前のマシン状態が記述されており、レジスタ`x12`にはスタックポインタが格納され、256ビットワードの`a`と`b`がそれぞれ`sp`および`sp+32`の位置に存在する。後件条件では、17回のRISC-Vステップ、つまり68バイトのコードが実行された後、`sp+32`の位置にあるワードがLeanの`BitVec 256`で定義されるビット単位のAND演算結果である`a &&& b`を格納していることが示されている。

この証明では、`runBlock`戦術を用いて各64ビットの構成要素ごとに1回ずつAND演算を行う4つの規格を組み合わせ、その後`cpsTripleWithin_weaken`を通じて`evmWordIs`という抽象化レベルへと昇華させる。

```lean
  -- 1. 各64ビット肢ごとのAND演算とスタックポインタ調整を組み合わせる（肢レベルの証明）
  have L0 := and_limb_spec 0 32 sp a0 b0 v7 v6 base...
  have L1 := and_limb_spec 8 40 sp a1 b1...
  have L2 := and_limb_spec 16 48 sp a2 b2...
  have L3 := and_limb_spec 24 56 sp a3 b3...
  have LADDI := addi_spec_gen_same_within.x12 sp 32...
  runBlock L0 L1 L2 L3 LADDI

  -- 2. EvmWord.getLimb_andという意味論的引理を用いてevmWordIsへ昇華する
  exact cpsTripleWithin_weaken...
    (fun h hp => by simp only [evmWordIs] at hp;... ; xperm_hyp hp)
    (fun h hq => by simp only [evmWordIs, EvmWord.getLimb_and];... ; xperm_hyp hq)
    h_main
```

Leanのコアは、個々の命令の意味論から最終的な`a &&& b`という結果に至るまで、すべてのステップをチェックします。外部のソルバーやSMTオラクルは一切必要ありません。

## プロジェクト構成

```
EvmAsm/
  Rv64/                       -- RV64IMバックエンド
    Basic.lean                --   マシン状態：レジスタ（64ビット）、メモリ、PC
    Instructions.lean         --   RV64IMの命令セットと意味論
    Program.lean              --   命令リストとしてのプログラム、順次的合成
    Execution.lean            --   分岐を考慮した実行、コードメモリ、step/stepN
    SepLogic.lean             --   分離論理のアサーションとコンビネータ
    CPSSpec.lean              --   CPSスタイルのHoareトリプル、分岐仕様、構造規則
    ControlFlow.lean          --   if_eqマクロ、記号的証明、pcIndep
    GenericSpecs.lean         --   命令にパラメータ化されたジェネリック仕様
    InstructionSpecs.lean     --   命令ごとのCPS仕様
    SyscallSpecs.lean         --   システムコール仕様：HALT、WRITE、read_input
    Tactics/
      PerfTrace.lean          --   パフォーマンストレースのインフラ
      XPerm.lean              --   xperm戦略：sepConjチェーンのAC置換
      XSimp.lean              --   xperm_hyp/xsimp戦略：アサーションの含意関係
      XCancel.lean            --   xcancel戦略：フレーム抽出を伴うキャンセル処理
      SeqFrame.lean           --   seqFrame戦略：自動的なフレーム生成と制限付きCPS仕様の合成
      LiftSpec.lean           --   liftSpec戦略：命令仕様の昇格処理
      RunBlock.lean           --   runBlock戦略：ブロック実行の自動化
      SpecDb.lean             --   @[spec_gen]属性と仕様データベース
  Evm64/                      -- RV64IM上でのEVMオペコード（4つの64ビット構成要素）
    Basic.lean                --   EvmWord（BitVec 256）、getLimb64、fromLimbs64
    Stack.lean                --   evmWordIs、evmStackIs、pcFreeといったレーマ
    EvmWordArith.lean         --   数学的正しさに関するレーマ（キャリチェーンなど）
    Compare/
      LimbSpec.lean           --   各構成要素ごとの共通比較仕様（lt、beq、slt_msb）
    Add/                      --   256ビットADD演算
      Program.lean            --     RV64プログラムの定義
      LimbSpec.lean           --     各構成要素ごとの仕様（add_limb0、add_limb_carry）
      Spec.lean               --     完全な合成処理とスタックレベルの仕様
    Sub/                      --   256ビットSUB演算（Add/と同じ構成）
    And/                      --   256ビットAND演算（Program + LimbSpec + Spec）
    Or/                       --   256ビットOR演算
    Xor/                      --   256ビットXOR演算
    Not/                      --   256ビットNOT演算
    Lt/                       --   256ビットLT演算（Program + Spec、Compare/LimbSpecを利用）
    Gt/                       --   256ビットGT演算
    Eq/                       --   256ビットEQ演算（Program + LimbSpec + Spec）
    IsZero/                   --   256ビットISZERO演算（Program + LimbSpec + Spec）
```
    Slt/                      --   256ビット符号付きSLT（Program + Spec、Compare/LimbSpecを使用）
    Sgt/                      --   256ビット符号付きSGT
    Pop/                      --   POP（Program + Spec）
    Push0/                    --   PUSH0（Program + Spec）
    Dup/                      --   DUP1-16（Program + Spec）
    Swap/                     --   SWAP1-16（Program + Spec）
    Multiply/                 --   MUL（Program + LimbSpec、教科書式4×4リム構造）
    DivMod/                   --   DIV/MOD（Program + LimbSpec + Compose、KnuthアルゴリズムD）
    SignExtend/               --   SIGNEXTEND（Program + LimbSpec + Compose + Spec）
    Shift/                    --   SHR/SHL/SAR（Program + LimbSpec + ShlSpec + SarSpec + Compose + ShlCompose + SarCompose + Semantic + ShlSemantic + SarSemantic）
    Byte/                     --   BYTE（Program + LimbSpec + Spec）
    zkvm-standards/           --   サブモジュール：zkVM RISC-Vターゲット標準
  Codegen/                    -- RV64アセンブリエミッター + プログラムレジストリ
    Programs.lean             --   `BuildUnit`プローブ用のレジストリハブ
    Programs/                 --   サブモジュール：Evm.lean、HashBridge.lean、
                              --     Ssz.lean、RlpRead.lean、Mpt.lean —
                              --     run_stateless_guestの一部を実装する
                              --     RV64マクロアセンブリヘルパー
                              --     （未検証のスケルトン；下記参照）
EvmAsm.lean                  -- トップレベルモジュールハブ
EvmAsm/Rv64.lean             -- Rv64モジュールハブ
EvmAsm/Evm64.lean            -- Evm64モジュールハブ
execution-specs/              -- サブモジュール：Ethereum実行仕様

## Codegenと実行

検証済みの `Program` は RV64 アセンブリとして出力され、アセンブル・リンクされた後、[Zisk](https://0xpolygonhermez.github.io/zisk/) エミュレータ（`ziskemu`）上で実行可能です。ロードマップや進捗状況については [CODEGEN.md](CODEGEN.md) をご覧ください。**M0–M10 の開発は完了しています**：テキストエミッタ、ビルド時の `#guard` ラウンドトリップテストによる全 `Instr` のカバレッジ確保、組み込みの `.data` セクションからも `ziskemu -i` を通じてプローバ入力からも `ziskemu` 上での `evm_add` 256ビットラウンドトリップテスト、実行時にフェッチ/デコード/ディスパッチを行う小型 EVM インタプリタ（M5a/M5b）、`tinyInterpRegistry` を通じた91のワイヤードオペコード（PUSH0–32, DUP1–16, SWAP1–16, 17の固定形状シングルトン、MLOAD/MSTORE/MSTORE8, DIV/MOD, トランポリンを介したSDIV/SMOD、インライン呼び出し可能なADDMODなど）、そして実行時バイトコードディスパッチャ（M8.5）により再帰テストセットの実行時間が約60秒から約20秒に短縮されています。Codegen-proofにより **Phase 1（レジストリの不変性）** および **Phase 4（ハンドラレベルの `cpsTripleWithin` スペック）** の最初の13/91件が `EvmAsm/Codegen/Proofs/` 下に公開されています。

クイックスタート：

```bash
# ziskemu上で検証済みのevm_addを生成し実行する：
lake exe codegen --program evm_add --halt linux93 -o gen-out/evm_add
ziskemu -e gen-out/evm_add.elf -o gen-out/evm_add.output

# エンドツーエンドのリグレッションスクリプト：
scripts/codegen-smoke.sh                            # M0のツールチェーン検証
scripts/codegen-evm_add-check.sh                    # M2の検証済みADD演算
scripts/codegen-evm_add-from-input-check.sh         # M4のziskemu -i経由でのADD演算
scripts/codegen-opcodes-runtime-check.sh            # M8.5の31ケースにおけるオペコードリグレッション検証
```

EEST stateless-guestコンプライアンスハーネスに関するドキュメントは
[docs/eest-stateless-testing.md](docs/eest-stateless-testing.md)に記載されており、
大量処理、フィルタリング、並列実行、オフセット再開、失敗数制限、
静音出力といった実行モードが含まれています。

セットアップ要件：`riscv64-elf-binutils`（または`riscv-gnu-toolchain`）および`ziskemu`です。Ziskエミュレータは、`bash <(curl -fsSL https://raw.githubusercontent.com/0xPolygonHermez/zisk/main/ziskup/install.sh)`を実行し、その後`~/.zisk/bin/ziskup --nokey -y`を実行して証明キーのダウンロードをスキップすることでインストールできます（エミュレータのみが必要なためです）。また、クロスツールチェーンを持たないCIホスト向けに、Codegenには`--asm-only`モードも用意されています。

### Stateless-guestのスケルトン（現在**未検証**）

`EvmAsm/Codegen/Programs.lean`（および`EvmAsm/Codegen/Programs/`下のサブモジュール）には、Ethereumの`run_stateless_guest`エントリポイントの一部を実装するRV64IMマクロアセンブリヘルパーが次第に増えてきています。これらにはRLPプリミティブ（`rlp_list_nth_item`、`rlp_encode_bytes`、`rlp_encode_list_prefix`など）、トランザクションフィールドアクセサ（レガシー／EIP-1559／EIP-2930／EIP-4844／EIP-7702デコーダ、イントリンシックガスヘルパ、署名抽出機能など）、アカウントおよびMPTプリミティブ（`account_decode`、`account_at_address`、`account_extract_*`、`mpt_walk`、`mpt_branch_*`、`mpt_compact_*`、`mpt_two_leaf_root_indexed`、`mpt_one_leaf_root_indexed`など）、ブロックボディヘルパ（`block_body_decode`、`block_count_transactions`、`block_validate_transactions_root_two_tx`、`block_validate_transactions_root_one_tx`、`block_validate_withdrawals_root_one_w`、`block_validate_withdrawals_root_two_w`、`block_validate_receipts_root_one_receipt`、`block_validate_receipts_root_two_receipts`、`block_hash_from_header`、`validate_parent_hash_link`、`validate_header_pair`、`validate_header_chain`、`block_validate_2tx_full`、`block_validate_1tx_full`、`block_validate_1tx_full_with_body`、`block_body_extract_2tx`、`block_body_extract_1tx`、`block_body_extract_tx_count`、`block_body_extract_withdrawal_count`、`block_body_summary`、`block_body_validate_empty`、`chain_body_total_tx_count`、`chain_body_total_withdrawal_count`、`block_validate_2tx_full_with_body`、`block_validate_empty_ommers_hash`、`block_validate_no_withdrawals_pair`、`block_validate_empty_receipts_root`、`block_validate_empty_block`、`validate_empty_block_with_parent`、`validate_empty_block_chain`、`block_hash_array_from_chain`、`validate_block_hash_chain_match`、`chain_compute_total_gas_used`、`chain_extract_number_range`、`header_extract_basefee`、`chain_extract_basefee_range`、`chain_block_hashes_commitment`、`header_extract_state_root`、`header_extract_parent_hash`、`header_extract_receipts_root`、`header_extract_transactions_root`、`header_extract_withdrawals_root`、`header_extract_ommers_hash`、`header_extract_prev_randao`、`header_extract_beneficiary`、`block_hash_matches`、`header_extract_gas_used`、`header_extract_gas_limit`、`block_validate_block_hash_pair`、`block_hash_and_extract_number`、`header_compute_summary_struct`、`header_extract_difficulty`、`header_extract_extra_data`、`header_extract_nonce`、`header_validate_nonce_zero`、`header_validate_difficulty_zero`、`validate_header_post_merge_zeros`、`chain_validate_post_merge_zeros`、`chain_validate_full`、`chain_validate_increasing_timestamps`、`chain_validate_consecutive_numbers`、`chain_extract_basefee_range`、`chain_validate_basefee_non_decreasing`、`chain_validate_basefee_non_increasing`、`chain_validate_gas_limit_constant`、`chain_validate_gas_limit_non_decreasing`が含まれます。
`chain_validate_gas_limit_non_increasing`、
`chain_extract_gas_limit_first_last`、
`chain_compute_total_gas_limit`、
`chain_extract_excess_blob_gas_first_last`、
`chain_compute_max_excess_blob_gas`、
`chain_compute_min_excess_blob_gas`、
`chain_compute_max_blob_count`、
`chain_compute_min_blob_count`、
`chain_extract_first_last_parent_beacon_block_root`、
`chain_extract_first_last_requests_hash`、
`header_extract_requests_hash`、
引き出し用のRLP/ハッシュなど）、およびアドレス生成機能（`address_compute_create`、`address_compute_create2`、`address_from_pubkey`）。これらの一覧は[`PLAN.md`](PLAN.md)内の`PR-K*`シリーズとして管理されている。

**これらのプログラムにはまだLean Hoare-tripleやCPS-specによる証明が存在しません。** 下記のStatusセクションにある「0 `sorry`、0 `axiom`」という不変条件は、検証済みのRV64コア、`EvmAsm/Evm64/<Op>/`下にある各オペコードハンドラー、および戦略／分離論理のインフラストラクチャに適用されます。Stateless-guestヘルパーは単なる骨組みに過ぎず、`lake exe codegen`によって生成された`def *Function : String`形式の生のASM本体として提供され、`BuildUnit`プローブを通じて登録され、`scripts/codegen-zisk-*-check.sh`フィックスチャ（各PRごとに1つのスクリプト）を利用して[`execution-specs`](https://github.com/ethereum/execution-specs/)のPythonリファレンスに対してziskemu上でエンドツーエンドでテストされます。これにより現時点で得られているものは以下の通りです：

# 厳格な制約
1. **構造の維持**：元のMarkdownデータ構造、インデント、見出し階層、表、リンク、URL、バッジ、コードブロック、インラインコードを一切変更しないこと。
2. **選択的翻訳**：ユーザーに表示される可視的な自然言語内容のみを翻訳すること。
3. **変更禁止**：コードタグ、キー名、変数プレースホルダー（{{var}}、${var}、%s、%dなど）、コマンド例、ファイルパス、プロジェクト名、API名、パッケージ名、モデル名、識別子、コード記号を翻訳したり変更したりすることは**厳禁**である。背景情報に既に対応する訳名が示されている場合を除く。
4. 用語、文体、固有名詞の翻訳は、与えられた背景情報と一致させること。

これによって得られないもの、そしてこれらのヘルパーがオペコードハンドラーと同等の地位を得る前に埋めなければならないギャップは以下の通りです：

- `cpsTripleWithin N`型のHoareトリプルが存在しない——ステップ数の制限となる`N`も、検証済みの前置き/後置き条件もない。
- ドキュメントコメントに記載された契約と実際に生成されたバイト列との間には機械的なチェックがなく、動作を固定するのはテストフィクスチャのみである。
- 現在、RLP、MPT、署名、アドレス導出用のヘルパーには**`@[spec_gen_rv64]`プレースホルダーが一切組み込まれておらず**、既存の自動化処理ではこれらを認識できない。

要するに、現時点ではこれらはプロセス記述によるテストコードに過ぎず、証明されたコードではない。今後のPRによって各ヘルパーごとの`Spec.lean`トリプルが追加され、未証明な部分が徐々に減少していくだろう。

## ビルド

```bash
# elan（Leanバージョン管理ツール）がまだインストールされていない場合はインストールする
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh

# Mathlibのキャッシュをダウンロードする（任意だが推奨される）
lake exec cache get

# プロジェクトをビルドする
lake build
```

### 依存関係

トップレベルのLake依存関係（[`lakefile.toml`](lakefile.toml)に記載）：

- **[Mathlib4](https://github.com/leanprover-community/mathlib4)** — Lean 4用の数学ライブラリ。`BitVec`や`Nat`演算、`Fin`、決定性問題の実装、および戦略処理の基盤として広く利用されている。  
- **Vendored Sail RISC-V model** (`vendor/sail-riscv-zkvm-lean/`) — 公式の[Sail RISC-Vモデル](https://github.com/riscv/sail-riscv)をベースにした、リリースバージョンが固定されたスコープ付きのLeanエクスポートで、RV64IMサブセット（`SAIL_MODULES = main I_insts M_insts`）のみを対象としている。このパッケージのlakefile内にあるgitで固定された`require`により、[lean-sail](https://github.com/sail-lean/lean-sail)（SailのLeanモナドランタイム）が読み込まれる。

  なぜベンドされたスコープ付き形式を採用するのか？このモデルはプロジェクトの信頼の拠点であるため、変更が頻繁に行われるフォークから取得するのではなく、プロジェクト内で管理・再現可能な形で扱われます。sail-riscvのリリースタグ、Sailコンパイラのバージョン、lean-sailのリビジョン、モジュールのスコープ、設定値、そしてcontent `model_sha256`といったすべての入力要素は[`sail-import/PROVENANCE.toml`](sail-import/PROVENANCE.toml)に記録されており、[`scripts/regen-sail-model.sh`](scripts/regen-sail-model.sh)を通じて再生成することが可能です。（これにより、以前利用していた変更が頻繁に行われる`dhsorens/sail-riscv-lean`フォークへの依存関係は廃止されました。）

ベンドされたSailモデルは、私たちのRISC-Vセマンティクスにおける**信頼の拠点**となっています。[`EvmAsm/Rv64/Instructions.lean`](EvmAsm/Rv64/Instructions.lean)にある手書きの仕様は、[`EvmAsm/Rv64/SailEquiv/`](EvmAsm/Rv64/SailEquiv/)内の抽象関係証明（`StateRel.lean`および各命令クラス別の`*Proofs.lean`）を通じて、Sailが生成したデコーダ/エクゼキューターと結びつけられています。これにより、公式のSailモデルに対して「あなたが手書きした命令セマンティクスは本当にRISC-Vなのか？」という要件を満たすことができるのです。

問題の追跡: [#84](https://github.com/Verified-zkEVM/evm-asm/issues/84)
（`sail-riscv-lean` を Lake dep としてインポート — 実装完了），
[#93](https://github.com/Verified-zkEVM/evm-asm/issues/93) （手書きの `Instr` を SAIL 生成の AST にマップする）。

### 毎週のビルドベンチマーク

定期的に実行されるGitHub Actionsワークフロー、
[`.github/workflows/benchmark.yml`](.github/workflows/benchmark.yml)により、
毎週月曜日のUTC 06:00に`lake build`が実行され、実行結果のジョブサマリーには
実際の経過時間やメモリ使用量の最大値が記録されます。また、
`/usr/bin/time -v`で出力された生データはビルドアーティファクトとして
(`benchmark-<run-id>`)としてアップロードされ、90日間保持されることで
以前の実行結果との差分比較によるレグレッション検出が可能になります。

このワークフローはPRのCIとは独立しており、どのプルリクエストの承認も制御しません。予定外に手動で実行するには、**Actions → Benchmark → Run workflow**（または`gh workflow run benchmark.yml`）に進んでください。長期間保存される実行履歴（`benchmark-history`というオーファンブランチ）やリグレッション検出用のワークフローについては、貢献者向けに[`AGENTS.md`](AGENTS.md)および[`docs/benchmark-workflow-design.md`](docs/benchmark-workflow-design.md)に記載されています。

このワークフローの構成は、実際のLeanプロジェクトのビルドベンチマークがどのようなものかを把握するのに役立った[`Beneficial-AI-Foundation/curve25519-dalek-lean-verify`](https://github.com/Beneficial-AI-Foundation/curve25519-dalek-lean-verify)のベンチマークCIに関する調査結果をもとに決定されました。設計の根拠は[`docs/benchmark-workflow-design.md`](docs/benchmark-workflow-design.md)に記載されています。

## ステータス

これはそのアプローチを示す**プロトタイプ**です。オペコードのカバレッジ、各オペコードごとのサイクル境界、コードジェネレーションの到達範囲、そして[`eth-act/zkvm-standards`](https://github.com/eth-act/zkvm-standards)や実行仕様書の参照基準への準拠状況といった主要な指標は、**[`PROGRESS.md`](PROGRESS.md)**にある単一の多次元ダッシュボード上で表示されており、これらはカーネルによってチェックされたレジストリ(`EvmAsm/Progress.lean`)から`[scripts/progress-report.sh`](scripts/progress-report.sh)によって再生成され、CIにおいても検証が行われます。

主要な不変条件：

- コードベース全体で**0件の`sorry`、0件の`axiom`**（`lake build` clean実行、CIにより強制適用）。
- 分離ロジック、ステップ制限付きCPS Hoareトリプル（`cpsTripleWithin N`）、および自動化された戦略（`xperm`、`xcancel`、`seqFrame`、`liftSpec`、`runBlock`）を備えた**検証済みのRV64IMコア**。
- **EVMオペコードのカバレッジ**：`EvmAsm.Evm64.EvmOpcode`に記載されている149のバイトコード（PUSH/DUP/SWAP/LOGファミリーを含む）ごとに、現在「検証済み」、「部分的」、「実行可能仕様のみ」、「未開始」といったカテゴリでオペコード別のカバレッジが記載されている[`PROGRESS.md`](PROGRESS.md)の表を参照。
- **コードジェネレーション**：[`CODEGEN.md`](CODEGEN.md)のM0–M10までが提供されている（テキストエミッタ、ランタイムディスパッチャを持つ小型EVMインタプリタ、DIV/MOD、SDIV/SMOD、ADDMODを含む91のワイヤードオペコード）。コードジェネレーションに関する第1フェーズの証明（レジストリの不変性）および第4フェーズの初期ハンドラ仕様（91件中13件）が完成している。
- **Stateless-guest scaffold**（`PR-K*`シリーズ）：RLP、MPT、トランザクションデコード、アカウント／ブロックボディアクセサ、アドレス導出用の、未検証のRV64マクロアセンブリヘルパ。各ヘルパにはPythonリファレンスを対象としたエンドツーエンドのziskemuフィクスチャが存在するが、**Hoareトリプル仕様はまだない**。検証状況や証明上のギャップについては上記の「Stateless-guest scaffold」セクションを参照のこと。
- **ロードマップ**：詳細なオペコード別計画は[`PLAN.md`](PLAN.md)に記載されており、L1-zkEVMコンテキストについては[`PROGRESS.md`](PROGRESS.md)の「L1-zkEVMスタックにおける役割」セクションで説明されている。

## ドキュメント

- [証明済みの注目すべき仕様](docs/notable-specs.md) — コミットで固定されたパーマリンクを持つスタック仕様および`EvmWord`の正しさに関する定理の一覧。

## 参考文献

- Kennedy, A., Benton, N., Jensen, J.B., Dagand, P.-E. (2013).
  "Coq: The world's best macro assembler?" PPDP 2013.
  https://www.microsoft.com/en-us/research/publication/coq-worlds-best-macro-assembler/
- **SPlean** (Separation Logic Proofs in Lean), Verse Lab.
  https://github.com/verse-lab/splean
  `Tactics/` 内の `xperm` / `xperm_hyp` / `xsimp` といった戦略は、
  SPlean の `xsimpl` 戦略に着想を得ています。
- **YOLO** — Mikhalchuk, V., Gladshtein, V., Sergey, I. (2026).
  "Lazy Proof Automation for Separation Logic." ITP 2026 (掲載予定).
  Artifact: https://github.com/verse-lab/yolo
  証明書ベースの順列証明器 `buildPermProofCert` / `seps_permute`
  （`Tactics/XPerm.lean` および `SepLogic.lean` 内にあり、`xperm.cert` オプションで
  アクセス可能）は、YOLO の核心的なアイデアを**再実装**しています。
  つまり、未検証の原子マッチング探索を一度だけ実行し、エグジット全体を
  単一の安価で検証済みのリプレイによって処理するのです。これは
  歩を追って証明を行う方法ではありません。これはYOLOのコードを移植したもの
  ではなく、そのアイデアを独立して再実装したものであり、YOLOの仕組み
  （`hprop` 構文木、左右のワークリスト、拡張可能な操作タグ型クラス、
  レコーデッド・タクティック・スクリプトのリプレイなど）は一切使用されて
  いません。代わりに結果をインデックス順列 `σ : List Nat` として記録し、
  `seps_permute` というレムマを一つ使ってそれを処理します。このレムマの
  `σ.Perm (List.range n)` という側条件は、単一のカーネル検証済みの
  `decide` によって閉じられます。高速な信頼できない単純化処理と
  単一の検証済み再構築処理を分離するという根本的なアイデアは、
  Mikhalchuk、Gladshtein、Sergey の功績です。
- Charguéraud, A. (2020). "Separation Logic for Sequential Programs
  (Functional Pearl)." *Proc. ACM Program. Lang.* 4, ICFP, Article 116.
  https://doi.org/10.1145/3408998
- **bedrock2**: https://github.com/mit-plv/bedrock2
  `Tactics/XCancel.lean` および `Tactics/SeqFrame.lean` 内のフレーム自動化戦略
  （`xcancel`、`seqFrame`）は、bedrock2 の分離論理自動化に着想を得ています。
  具体的には：
  - `bedrock2/src/bedrock2/SepLogAddrArith.v` の `wcancel` 戦略（127行～134行）
    は、タグ＋アドレスによる原子のマッチングや、マッチしなかった仮説原子の
    残差としてフレームを計算するというキャンセル手法のヒントとなりました。
  - `bedrock2/src/bedrock2/FrameRule.v` のフレームルールインフラストラクチャ（75行～175行）
    は、スペックに普遍的なフレームパラメータが含まれ、戦略が組み合わせ時に
    それをインスタンス化するという自動的なフレーム抽出パターンのヒントとなりました。
  - `compiler/src/compiler/GoFlatToRiscv.v` 内の明示的なフレームを持つ命令スペック（439行～546行）
    は、`cpsTriple_frameR` および `cpsTriple_seq_perm_same_cr` を使って命令スペックを
    組み合わせる設計の参考となりました。
- Knuth, D.E. (1997). *The Art of Computer Programming, Volume 2:
『半数値アルゴリズム』*（第3版）、§4.3.1「古典的なアルゴリズム」。Addison-Wesley社。`Evm64/DivMod.lean`におけるDIV/MOD命令コードにはアルゴリズムDが使用されている。
- zkvm-standards: https://github.com/eth-act/zkvm-standards
  zkVM RISC-Vターゲット、I/Oインターフェース、およびCインターフェースアクセラレータの規格。`EvmAsm/Evm64/zkvm-standards/standards/c-interface-accelerators/zkvm_accelerators.h`にある提供されているヘッダは、暗号化プリコンパイル、KECCAK256、secp256k1の検証のために検証済みゲストが対象とする標準的なアクセラレータC ABIであり、決定記録、完全な設計ノート、各プリコンパイルのカバレッジやEVMプリコンパイル→アクセラレータのマッピング表については[`docs/zkvm-accelerators-interface.md`](docs/zkvm-accelerators-interface.md)を参照のこと。
- ホストI/O C ABI（唯一の真実源）：
  `EvmAsm/Evm64/zkvm-standards/standards/io-interface/README.md`には、標準的なホストI/Oインターフェース（`read_input` / `write_output`）が定義されている。決定記録、SP1の`HINT_LEN` / `HINT_READ` / `COMMIT`→zkvm-standardsのマッピング、およびbeadsの親プロジェクト`evm-asm-96ysd`で追跡されている移行計画（GH #114 / #116）については[`docs/zkvm-host-io-interface.md`](docs/zkvm-host-io-interface.md)を参照のこと。
- SP1 zkVM: https://github.com/succinctlabs/sp1
  RISC-Vの`ECALL`フレーミング（命令エンコーディング、レジスタ規約、`a0`経由での戻り）はSP1が使用するのと同じメカニズムに従っている。*関数セット*や引数のレイアウトはSP1のシステムコールテーブルではなく`zkvm_accelerators.h`に従う。具体的なシステムコールIDはホスト側の詳細であり、ECALLハンドラ内で再マッピングされ、beadsの親プロジェクト`evm-asm-nr2sk`内でブリッジごとに追跡される。
- sail-riscv-lean: https://github.com/opencompl/sail-riscv-lean
- RISC-V ISA仕様書: https://riscv.org/technical/specifications/
