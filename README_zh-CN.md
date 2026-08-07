# evm.asm：用于在Lean 4中构建zkEVM的经过验证的宏汇编器（早期实验版本）

<!-- hy-mt2-i18n:start -->
[Español](./README.md) | **中文** | [English](./README_en.md) | [日本語](./README_ja.md)
<!-- hy-mt2-i18n:end -->


一个针对zkEVM的经过验证的宏汇编器的原型实现，基于RISC-V RV64IM后端构建，其设计灵感来源于：

> Andrew Kennedy、Nick Benton、Jonas B. Jensen、Pierre-Evariste Dagand。
> **《Coq：全球最出色的宏汇编器？》**
> *第15届声明式编程原理与实践国际研讨会（PPDP 2013）论文集*，2013年9月，ACM出版。
> https://www.microsoft.com/en-us/research/publication/coq-worlds-best-macro-assembler/

## 警告：仅为实验性原型

**切勿将此项目用于任何重要用途。**

这只是一个存在诸多局限性的实验性研究原型：

- **不遵循 RISC-V 规范**：指令语义是通过特定方式生成的，并未经过官方 RISC-V 规范的验证，因此可能存在与实际 RISC-V 行为细微（或相当明显）的差异。  
- **不遵循 EVM 规范**：示例中所用的规范同样是通过该方式生成的，也未经过 EVM 规范的验证。  
- **缺乏一致性测试**：目前尚未进行任何系统性测试来确认该实现是否与真实的 RISC-V 处理器或模拟器兼容，针对 EVM 的测试也同样没有开展。  
- **原型级质量**：这段代码仅用于教育和研究目的，旨在探索经过验证的宏汇编技术，绝不可用于实际生产环境。

## 动机：在zkEVM中消除对编译器的信任

使用zkVM的常规方式是将高级程序编译为RISC-V汇编代码，再借助零知识证明系统来验证其执行轨迹的正确性。该证明能够覆盖*执行轨迹*，却无法涵盖*编译器*本身。如果编译器存在漏洞或被恶意篡改，即便零知识证明是有效的，源代码也是正确的，该证明仍可能与开发者（或接收方）的预期不符。

**evm.asm**探索了一种替代方案：直接将程序编写为RISC-V代码，并在生成任何ZK证明之前，先在Lean 4中*证明*其正确性。这样做的目标是让开发者（或ZK证明的接收者）无需再信任用于生成客程序的编译器。

更具体而言，evm.asm 的目标是构建 **zkEVM** 的客户端部分。对于这种应用场景而言，缩小可信计算基础至关重要。

### 在 L1-zkEVM 架构中的角色

其目标形态是一种可供L1 zkVM证明器使用的**无状态区块验证器**ELF文件——这与目前[`eth-act/ere-guests`](https://github.com/eth-act/ere-guests)中由Rust编译生成的`stateless-validator-{reth,ethrex}`二进制文件所占据的位置相同。evm.asm同样遵循相同的接口规范（根据[`eth-act/zkvm-standards`](https://github.com/eth-act/zkvm-standards)的IO接口，输入为`(block, execution_witness)`，输出为处理后的状态根），但它是从经过验证的RV64核心自下而上构建的，而非基于高级EL客户端，因此该程序包含从输入的RLP字节到最终状态根的、经Lean内核验证的Hoare三元组——在可信计算基中不存在编译器。此类程序的基准测试可在[`eth-act/zkevm-benchmark-workload`](https://github.com/eth-act/zkevm-benchmark-workload)以及[L1 zkEVM基准测试博客](https://zkevm.ethereum.foundation/blog/benchmarking-zkvms)中找到。

与执行层客户端的集成属于未来的工作内容；有关9项客程序检查清单以及多维度状态仪表板的信息，请参阅[`PROGRESS.md`](PROGRESS.md)。

第二个动机在于，我们的霍尔三元组在步数上是*有限制*的（`cpsTripleWithin N base...`）：每个规范都明确给出了程序执行的RISC-V步数上限`N`。由此带来两个后果：

# 严格约束
1. **结构锁定**：绝对保持原有的 Markdown 数据结构、缩进、标题层级、表格、链接、URL、徽章、代码块和行内代码完全不变。
2. **选择性翻译**：仅翻译面向用户展示的可见自然语言内容。
3. **禁止修改**：**严禁**翻译或更改代码标签、键名、变量占位符（如 {{var}}、${var}、%s、%d 等）、命令示例、文件路径、项目名、API 名、包名、模型名、标识符和代码符号；除非背景信息中已经给出对应译名。
4. 术语、风格、专有名词的译法要与所给背景信息保持一致。

【待翻译片段】
1. **zkVM循环次数限制**。`N` 是一个最坏情况下的循环预算值，可在各个组合的宏之间求和，用以确保客程序在无需实际运行时仍能符合zkVM每次证明的处理上限。
2. **Gas成本**。`N` 是经过验证的每条操作码对应的指令数量，它是构建合理Gas定价模型的主要输入参数。

## 核心理念

Lean 4 同时承担着以下功能：

1. **汇编器**：指令属于归纳类型；程序则是通过顺序组合（`;;`）连接而成的指令列表。
2. **宏语言**：能够生成程序的Lean函数即充当了宏的角色，可利用Lean的所有功能（递归、模式匹配、条件判断等）。
3. **规范语言**：包含分离逻辑断言的Hoare三元组用于描述EVM操作码及宏组合的正确性属性。
4. **证明助手**：Lean的核心机制可无需外部验证源即可确认宏符合其规范要求。

## 示例：经过验证的 EVM 指令码长什么样

每个 EVM 指令码都是通过一系列针对 4×64 位数据段的 RISC-V 指令来实现的。**栈级规范**借助 `evmWordIs` 将这种低级实现与 256 位 EVM 的语义联系起来——该断言指出四个连续的内存字共同构成一个 `EvmWord`（即 `BitVec 256`）。

```lean
-- 一个 EvmWord 存储在连续地址上的 4 个 64 位字段中
def evmWordIs (addr : Addr) (v : EvmWord) : Assertion :=
  (addr ↦ₘ v.getLimb 0) ** ((addr + 8) ↦ₘ v.getLimb 1) **
  ((addr + 16) ↦ₘ v.getLimb 2) ** ((addr + 24) ↦ₘ v.getLimb 3)
```

以下是256位AND操作码的栈级规范（位于`EvmAsm/Evm64/And/Spec.lean`中）。该规范指出：从栈上的两个`EvmWord` `a`和`b`开始，由17条指令组成的RISC-V程序`evm_and_code`能够计算出`a &&& b`的结果——并且还有经过机器验证的证明支持。

```lean
/-- 基于栈层的256位EVM与运算：通过evmWordIs对两个EvmWord进行操作。 -/
theorem evm_and_stack_spec (sp base : Addr)
    (a b : EvmWord) (v7 v6 : Word)
    (hvalid : ValidMemRange sp 8) :
    let code := evm_and_code base
    cpsTripleWithin 17 base (base + 68) code
      (-- 前置条件：栈指针、临时寄存器以及两个256位字
       (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ v7) ** (.x6 ↦ᵣ v6) **
       evmWordIs sp a ** evmWordIs (sp + 32) b)
      (-- 后置条件：栈指针向前移动，结果为a &&& b
       (.x12 ↦ᵣ (sp + 32)) ** (.x7 ↦ᵣ (a.getLimb 3 &&& b.getLimb 3)) **
       (.x6 ↦ᵣ b.getLimb 3) **
       evmWordIs sp a ** evmWordIs (sp + 32) (a &&& b))
```

该陈述是一个带有分离逻辑断言的有界Hoare三元组（`cpsTripleWithin`）。前置条件描述了执行前的机器状态：寄存器`x12`保存着栈指针，而两个256位字`a`和`b`分别位于`sp`地址和`sp+32`地址处。后置条件则表明，在运行68字节的代码、即17个RISC-V指令步之后，`sp+32`地址处的字现在存储着`a &&& b`——也就是由Lean的`BitVec 256`定义的按位与运算结果。

该证明通过`runBlock`策略组合了四个针对各位的规范（每个64位位组对应一个与操作），随后借助`cpsTripleWithin_weaken`将其提升至`evmWordIs`抽象层。

```lean
  -- 1. 组合4个各64位分支的按位与操作以及栈指针调整（分支级证明）
  have L0 := and_limb_spec 0 32 sp a0 b0 v7 v6 base...
  have L1 := and_limb_spec 8 40 sp a1 b1...
  have L2 := and_limb_spec 16 48 sp a2 b2...
  have L3 := and_limb_spec 24 56 sp a3 b3...
  have LADDI := addi_spec_gen_same_within.x12 sp 32...
  runBlock L0 L1 L2 L3 LADDI

  -- 2. 利用 EvmWord.getLimb_and 的语义引理提升至 evmWordIs 形式
  exact cpsTripleWithin_weaken...
    (fun h hp => by simp only [evmWordIs] at hp;... ; xperm_hyp hp)
    (fun h hq => by simp only [evmWordIs, EvmWord.getLimb_and];... ; xperm_hyp hq)
    h_main
```

Lean的内核会逐一检查每一步——从单个指令的语义到最终的 `a &&& b` 计算结果。无需任何外部求解器或SMT预言机。

## 项目结构

```
EvmAsm/
  Rv64/                       -- RV64IM后端
    Basic.lean                --   机器状态：寄存器（64位）、内存、程序计数器
    Instructions.lean         --   RV64IM指令集及其语义
    Program.lean              --   作为指令列表的程序及顺序组合方式
    Execution.lean            --   考虑分支情况的执行过程、代码内存、单步/多步执行
    SepLogic.lean             --   分离逻辑断言与组合子
    CPSSpec.lean              --   CPS风格的Hoare三元组、分支规范、结构规则
    ControlFlow.lean          --   if_eq宏、符号化证明、pcIndep相关内容
    GenericSpecs.lean         --   基于指令参数化的通用规范
    InstructionSpecs.lean     --   每条指令对应的CPS规范
    SyscallSpecs.lean         --   系统调用规范：HALT、WRITE、read_input
    Tactics/
      PerfTrace.lean          --   性能追踪基础设施
      XPerm.lean              --   xperm策略：sepConj链的AC排列操作
      XSimp.lean              --   xperm_hyp/xsimp策略：断言蕴含关系处理
      XCancel.lean            --   xcancel策略：结合帧提取的取消操作
      SeqFrame.lean           --   seqFrame策略：自动构建带边界约束的CPS规范
      LiftSpec.lean           --   liftSpec策略：提升指令规范
      RunBlock.lean           --   runBlock策略：块级执行自动化处理
      SpecDb.lean             --   @[spec_gen]属性及规范数据库
  Evm64/                      -- RV64IM上的EVM操作码（4个64位组成）
    Basic.lean                --   EvmWord（BitVec 256）、getLimb64、fromLimbs64函数
    Stack.lean                --   evmWordIs、evmStackIs、pcFree相关引理
    EvmWordArith.lean         --   数学正确性相关引理（进位链等）
    Compare/
      LimbSpec.lean           --   各组成部分共用的比较规范（lt、beq、slt_msb）
    Add/                      --   256位加法运算
      Program.lean            --     RV64程序定义
      LimbSpec.lean           --     各组成部分的加法规范（add_limb0、add_limb_carry）
      Spec.lean               --     完整的组合规范及栈级规范
    Sub/                      --   256位减法运算（结构与Add/相同）
    And/                      --   256位与运算（包含程序、组件规范及整体规范）
    Or/                       --   256位或运算
    Xor/                      --   256位异或运算
    Not/                      --   256位非运算
    Lt/                       --   256位小于运算（基于程序及规范，使用Compare/LimbSpec）
    Gt/                       --   256位大于运算
    Eq/                       --   256位等于运算（基于程序、组件规范及整体规范）
    IsZero/                   --   256位是否为零运算（基于程序、组件规范及整体规范）
```
    Slt/                      --   256位带符号SLT运算（程序+规范，使用Compare/LimbSpec）
    Sgt/                      --   256位带符号SGT运算
    Pop/                      --   POP指令（程序+规范）
    Push0/                    --   PUSH0指令（程序+规范）
    Dup/                      --   1到16次复制操作（程序+规范）
    Swap/                     --   1到16次交换操作（程序+规范）
    Multiply/                 --   MUL乘法运算（程序+LimbSpec，采用教材中的4×4分支结构）
    DivMod/                   --   DIV除法与MOD取模运算（程序+LimbSpec+Compose，使用Knuth算法D）
    SignExtend/               --   符号扩展运算（程序+LimbSpec+Compose+Spec）
    Shift/                    --   SHR右移/SHL左移/SAR算术右移运算（程序+LimbSpec+ShlSpec+SarSpec+Compose+ShlCompose+SarCompose+Semantic+ShlSemantic+SarSemantic）
    Byte/                     --   BYTE字节操作（程序+LimbSpec+规范）
    zkvm-standards/           --   子模块：zkVM RISC-V目标标准
  Codegen/                    -- RV64汇编代码生成器+程序注册表
    Programs.lean             --   `BuildUnit`探测器的注册表中心
    Programs/                 --   子模块：Evm.lean、HashBridge.lean、
                              --     Ssz.lean、RlpRead.lean、Mpt.lean ——
                              --     用于实现run_stateless_guest部分功能的RV64宏汇编辅助模块
                              --     （尚未经过验证的框架；详见下文）
EvmAsm.lean                  -- 最顶层模块中心
EvmAsm/Rv64.lean             -- Rv64模块中心
EvmAsm/Evm64.lean            -- Evm64模块中心
execution-specs/              -- 子模块：以太坊执行规范

## 代码生成与执行

经过验证的 `Program` 可以被生成为 RV64 汇编代码，经汇编、链接后可在 [Zisk](https://0xpolygonhermez.github.io/zisk/) 模拟器（`ziskemu`）上运行。具体路线图与进展情况请参见 [CODEGEN.md](CODEGEN.md)。**M0–M10 阶段已完成**：文本生成器、具备构建时 `#guard` 往返测试的完整 `Instr` 覆盖率、通过内置 `.data` 区段以及通过 `ziskemu -i` 接入证明器输入在 `ziskemu` 上对 `evm_add` 进行的 256 位往返测试、带有运行时获取/解码/调度功能的微型 EVM 解释器（M5a/M5b）、通过 `tinyInterpRegistry` 定义的 91 个有线操作码（PUSH0–32、DUP1–16、SWAP1–16、17 个固定结构的单一操作码、MLOAD/MSTORE/MSTORE8、DIV/MOD、通过跳板实现的 SDIV/SMOD、通过内联调用实现的 ADDMOD），以及一个运行时字节码调度器（M8.5），它将回归测试的时间从约 60 秒缩短至约 20 秒。Codegen 已完成了**第一阶段（注册表不变量）**的证明，以及**第四阶段（处理程序级 `cpsTripleWithin` 规范）**中的前 13/91 个实例，相关成果已存放在 `EvmAsm/Codegen/Proofs/` 目录下。

快速入门：

```bash
# 在 Ziskemu 上生成并运行已验证的 evm_add：
lake exe codegen --program evm_add --halt linux93 -o gen-out/evm_add
ziskemu -e gen-out/evm_add.elf -o gen-out/evm_add.output

# 端到端回归测试脚本：
scripts/codegen-smoke.sh                            # M0 阶段工具链验证
scripts/codegen-evm_add-check.sh                    # M2 阶段已验证的 ADD 操作
scripts/codegen-evm_add-from-input-check.sh         # M4 阶段通过 ziskemu -i 输入的 ADD 操作验证
scripts/codegen-opcodes-runtime-check.sh            # M8.5 阶段 31 种操作码的回归测试
```

EEST 无状态访客合规性测试工具的文档位于 [docs/eest-stateless-testing.md](docs/eest-stateless-testing.md) 中，其中介绍了批量处理、过滤、并行运行、偏移恢复、失败次数限制以及静默输出等运行模式。

环境准备要求：`riscv64-elf-binutils`（或 `riscv-gnu-toolchain`）以及 `ziskemu`。Zisk 模拟器可通过 `bash <(curl -fsSL https://raw.githubusercontent.com/0xPolygonHermez/zisk/main/ziskup/install.sh)` 安装，随后运行 `~/.zisk/bin/ziskup --nokey -y` 即可跳过证明密钥的下载步骤（我们仅需模拟器本身）。对于没有交叉工具链的 CI 环境，Codegen 还提供了 `--asm-only` 模式。

### 无状态客机框架（目前**未经验证**）

`EvmAsm/Codegen/Programs.lean`（以及`EvmAsm/Codegen/Programs/`下的子模块）中存放着日益增多的RV64IM宏汇编辅助工具，这些工具实现了Ethereum `run_stateless_guest`入口点的部分功能——RLP原语（如`rlp_list_nth_item`、`rlp_encode_bytes`、`rlp_encode_list_prefix`等）、交易字段访问器（传统格式/EIP-1559/EIP-2930/EIP-4844/EIP-7702解码器、内在气费辅助函数、签名提取功能等）、账户与MPT原语（如`account_decode`、`account_at_address`、`account_extract_*`、`mpt_walk`、`mpt_branch_*`、`mpt_compact_*`、`mpt_two_leaf_root_indexed`、`mpt_one_leaf_root_indexed`等）、区块体辅助函数（如`block_body_decode`、`block_count_transactions`、`block_validate_transactions_root_two_tx`、`block_validate_transactions_root_one_tx`、`block_validate_withdrawals_root_one_w`、`block_validate_withdrawals_root_two_w`、`block_validate_receipts_root_one_receipt`、`block_validate_receipts_root_two_receipts`、`block_hash_from_header`、`validate_parent_hash_link`、`validate_header_pair`、`validate_header_chain`、`block_validate_2tx_full`、`block_validate_1tx_full`、`block_validate_1tx_full_with_body`、`block_body_extract_2tx`、`block_body_extract_1tx`、`block_body_extract_tx_count`、`block_body_extract_withdrawal_count`、`block_body_summary`、`block_body_validate_empty`、`chain_body_total_tx_count`、`chain_body_total_withdrawal_count`、`block_validate_2tx_full_with_body`、`block_validate_empty_ommers_hash`、`block_validate_no_withdrawals_pair`、`block_validate_empty_receipts_root`、`block_validate_empty_block`、`validate_empty_block_with_parent`、`validate_empty_block_chain`、`block_hash_array_from_chain`、`validate_block_hash_chain_match`、`chain_compute_total_gas_used`、`chain_extract_number_range`、`header_extract_basefee`、`chain_extract_basefee_range`、`chain_block_hashes_commitment`、`header_extract_state_root`、`header_extract_parent_hash`、`header_extract_receipts_root`、`header_extract_transactions_root`、`header_extract_withdrawals_root`、`header_extract_ommers_hash`、`header_extract_prev_randao`、`header_extract_beneficiary`、`block_hash_matches`、`header_extract_gas_used`、`header_extract_gas_limit`、`block_validate_block_hash_pair`、`block_hash_and_extract_number`、`header_compute_summary_struct`、`header_extract_difficulty`、`header_extract_extra_data`、`header_extract_nonce`、`header_validate_nonce_zero`、`header_validate_difficulty_zero`、`validate_header_post_merge_zeros`、`chain_validate_post_merge_zeros`、`chain_validate_full`、`chain_validate_increasing_timestamps`、`chain_validate_consecutive_numbers`、`chain_extract_basefee_range`、`chain_validate_basefee_non_decreasing`、`chain_validate_basefee_non_increasing`、`chain_validate_gas_limit_constant`、`chain_validate_gas_limit_non_decreasing`）。
`chain_validate_gas_limit_non_increasing`、`chain_extract_gas_limit_first_last`、`chain_compute_total_gas_limit`、`chain_extract_excess_blob_gas_first_last`、`chain_compute_max_excess_blob_gas`、`chain_compute_min_excess_blob_gas`、`chain_compute_max_blob_count`、`chain_compute_min_blob_count`、`chain_extract_first_last_parent_beacon_block_root`、`chain_extract_first_last_requests_hash`、`header_extract_requests_hash`，以及提现相关的 RLP/哈希等功能，还有地址派生功能（`address_compute_create`、`address_compute_create2`、`address_from_pubkey`）。这些程序的清单记录在 [`PLAN.md`](PLAN.md) 中的 `PR-K*` 系列下。

**这些程序目前还不存在 Lean Hoare-triple / CPS-spec 证明。** 下方 Status 部分中“0 `sorry`，0 `axiom`”这一不变式适用于已验证的 RV64 核心、`EvmAsm/Evm64/<Op>/` 下的各操作码处理函数，以及策略/分离逻辑基础设施。那些无状态访客辅助函数仅属于框架性质：它们以 `def *Function : String` 的形式提供由 `lake exe codegen` 生成的原始汇编代码体，通过 `BuildUnit` 探针进行注册，并借助 `scripts/codegen-zisk-*-check.sh` 固定装置在 ziskemu 上针对 [`execution-specs`](https://github.com/ethereum/execution-specs/) 的 Python 参考实现进行端到端测试（每个 PR 对应一个脚本）。这就是我们目前所拥有的情况：

- 每个辅助函数都在 ziskemu 上针对相应的 Python 参考测试用例进行构建与执行；CI 会在每个 PR 中重新运行这些相同的测试用例。
- 函数签名、内存布局以及副作用约束均记录在每个 `*Function` def 语句上方的文档注释中（包括“调用约定”、“组合关系”和“状态”部分），这些内容将成为未来 Hoare 三重形式的文字形式前置条件。
- 最终证明树中的每个 `Spec.lean` 位置都会通过一行占位符预先预留，从而确保从一开始导入关系就保持稳定。

它未能为我们提供的——以及在这些辅助函数能够与操作码处理函数处于同等地位之前仍需填补的差距：

- 没有 `cpsTripleWithin N` 类型的霍尔三元组——既没有步长限制的 `N`，也没有经过验证的前提/后置条件。
- 文档注释中的契约与生成的字节码之间不存在机器可检查的关联；仅有测试固定装置能够约束行为。
- 目前，RLP、MPT、签名以及地址派生相关的辅助工具**没有接入 `@[spec_gen_rv64]` 占位符**，因此现有的自动化工具无法检测到它们。

简而言之：目前这些仍是带有自然语言规格的测试代码，而非已被证明的代码。未来的提交将会为每个辅助函数添加 `Spec.lean` 三元组，从而逐步减少未经证明的部分。

## 构建项目

```bash
# 若尚未安装 elan（Lean 版本管理工具），请先进行安装
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh

# 下载 Mathlib 缓存（可选，但建议执行）
lake exec cache get

# 构建项目
lake build
```

### 依赖项

Lake顶层依赖项（在[`lakefile.toml`](lakefile.toml)中声明）：

- **[Mathlib4](https://github.com/leanprover-community/mathlib4)** — Lean 4的数学库，被广泛用于实现`BitVec`、`Nat`运算、`Fin`类型、可判定性实例以及策略框架等功能。  
- **内置的Sail RISC-V模型**（`vendor/sail-riscv-zkvm-lean/`）——这是官方[Sail RISC-V模型](https://github.com/riscv/sail-riscv)经过版本锁定且具有作用域限制的Lean导出版本，仅包含RV64IM子集（`SAIL_MODULES = main I_insts M_insts`）。该模型通过内置包的lakefile中经过git锁定的`require`语句引入了[`lean-sail`](https://github.com/sail-lean/lean-sail)，即Sail的Lean单子运行时环境。

  为何要采用预置且范围受限的方式？该模型是项目的信任基石，因此由其自身掌控并确保可复现，而非从不断变动的分支中获取：所有输入——包括sail-riscv的版本标签、Sail编译器版本、lean-sail的修订号、模块范围、配置以及内容校验值`model_sha256`——都会被记录在[`sail-import/PROVENANCE.toml`](sail-import/PROVENANCE.toml)中，并可通过[`scripts/regen-sail-model.sh`](scripts/regen-sail-model.sh)重新生成。（这取代了之前对不断变动的`dhsorens/sail-riscv-lean`分支的依赖。）

所引入的预打包版Sail模型是我们RISC-V语义的**信任锚点**：位于[`EvmAsm/Rv64/Instructions.lean`](EvmAsm/Rv64/Instructions.lean)中的手写规范，通过[`EvmAsm/Rv64/SailEquiv/`](EvmAsm/Rv64/SailEquiv/)中的抽象关系证明（即`StateRel.lean`文件以及针对各类指令的`*Proofs.lean`文件）与由Sail生成的解码器/执行器相关联。正是依靠这种方式，我们才能向官方的Sail模型证明“我们所编写的手写指令语义确实符合RISC-V标准”。

问题跟踪：[#84](https://github.com/Verified-zkEVM/evm-asm/issues/84)（将 `sail-riscv-lean` 作为 Lake 依赖导入——已完成），[#93](https://github.com/Verified-zkEVM/evm-asm/issues/93）（将手写的 `Instr` 映射到 SAIL 生成的抽象语法树）。

### 每周构建基准测试

有一个按计划运行的 GitHub Actions 工作流，即[`.github/workflows/benchmark.yml`](.github/workflows/benchmark.yml)，它会在每周一世界标准时间 06:00 执行 `lake build` 操作，并在相应任务的摘要中记录实际耗时以及内存峰值占用大小。`/usr/bin/time -v` 的原始输出结果会被作为构建产物（命名为 `benchmark-<run-id>`）上传，保留时长为 90 天，以便通过对比分析发现功能退化问题。

该工作流与 PR 的 CI 流水线相互独立，不会对任何拉取请求设置审核关卡。如需手动触发非定时运行，可前往 **Actions → Benchmark → Run workflow**（或执行 `gh workflow run benchmark.yml`）。关于长期保留的运行历史记录（`benchmark-history` 孤立分支）以及用于检测回归问题的工作流，相关说明已记录在 [`AGENTS.md`](AGENTS.md) 和 [`docs/benchmark-workflow-design.md`](docs/benchmark-workflow-design.md) 中，供贡献者参考。

该工作流的架构设计参考了[`Beneficial-AI-Foundation/curve25519-dalek-lean-verify`](https://github.com/Beneficial-AI-Foundation/curve25519-dalek-lean-verify)的基准测试CI流程，通过分析该流程有助于了解实际中的Lean项目构建基准测试应具备怎样的形态。其设计理念详见[`docs/benchmark-workflow-design.md`](docs/benchmark-workflow-design.md)。

## 状态

这是一个用于展示该方法的**原型**。各项核心指标——操作码覆盖率、各操作码的周期上限、代码生成覆盖范围，以及与[`eth-act/zkvm-standards`](https://github.com/eth-act/zkvm-standards)及执行规范参考文档的符合程度——均显示在**[`PROGRESS.md`](PROGRESS.md)**中的单个多维仪表板上，这些数据由`[scripts/progress-report.sh`](scripts/progress-report.sh)从经过内核校验的注册表(`EvmAsm/Progress.lean`)中生成，并在持续集成过程中进行验证。

核心指标恒定值：

- 整个代码库中**不存在** `sorry` 或 `axiom`（通过 `lake build` 清理操作及CI检查确保）。
- 拥有经过验证的RV64IM核心，包含分离逻辑、带步长限制的CPS Hoare三元组（`cpsTripleWithin N`），以及自动化策略（`xperm`、`xcancel`、`seqFrame`、`liftSpec`、`runBlock`）。
- **EVM指令集覆盖率**：请参阅[`PROGRESS.md`](PROGRESS.md)中的覆盖率表格——针对 `EvmAsm.Evm64.EvmOpcode` 中的149种字节码（已扩展PUSH/DUP/SWAP/LOG系列），当前会按指令集跟踪已证明、部分证明、仅符合可执行规范以及尚未开始验证的各类情况。
- **代码生成**：[`CODEGEN.md`](CODEGEN.md)中M0–M10阶段的内容已实现（包括文本输出器、带有运行时调度器的微型EVM解释器，以及包含DIV/MOD、SDIV/SMOD、ADDMOD在内的91种硬件指令）；代码生成相关的第一阶段（注册表不变量）证明以及第四阶段的初始处理程序规范（91种中的13种）也已完成。
- **无状态访客框架**（`PR-K*`系列）：为RLP、MPT、交易解码、账户/区块体访问器以及地址推导等功能提供了未经验证的RV64宏汇编辅助工具。每个辅助工具都配有针对Python参考实现的端到端ziskemu测试用例，但**目前尚无Hoare三元组规范**；有关验证状态及证明缺口的信息，请参见上文的“无状态访客框架”小节（#stateless-guest-scaffold-currently-unproved）。
- **路线图**：详细的逐指令计划详见[`PLAN.md`](PLAN.md)；L1-zkEVM相关内容则位于[`PROGRESS.md`](PROGRESS.md)“在L1-zkEVM堆栈中的角色”一节。

## 文档资料

- [已验证的重要规范](docs/notable-specs.md) —— 包含堆栈规范及`EvmWord`正确性定理的索引，配有固定链接。

## 参考文献

- Kennedy, A., Benton, N., Jensen, J.B., Dagand, P.-E. (2013).
  “Coq：世界上最好的宏汇编器？”PPDP 2013。
  https://www.microsoft.com/en-us/research/publication/coq-worlds-best-macro-assembler/
- **SPlean**（Lean中的分离逻辑证明），Verse Lab。
  https://github.com/verse-lab/splean
  `Tactics/`中的`xperm` / `xperm_hyp` / `xsimp`策略灵感来源于SPlean的`xsimpl`策略。
- **YOLO** — Mikhalchuk, V., Gladshtein, V., Sergey, I. (2026).
  “分离逻辑的惰性证明自动化。”ITP 2026（即将发表）。
  相关代码：https://github.com/verse-lab/yolo
  基于证书的排列证明工具`buildPermProofCert` / `seps_permute`
  （位于`Tactics/XPerm.lean`和`SepLogic.lean`中，需通过`xperm.cert`选项启用）**重新实现了YOLO的核心思想**——仅执行一次未经验证的原子匹配搜索，然后通过*单个*低成本且经过验证的重放操作即可推导出整个蕴含关系，而非逐步进行验证证明。这是一种**独立的重新实现，并非YOLO代码的移植**：它不使用YOLO的任何机制（没有`hprop`语法树，没有左右工作列表，没有可扩展的操作标签类型类，也没有记录策略脚本的重放功能）。相反，它会将结果记录为索引排列`σ : List Nat`，并通过一个`seps_permute`引理来推导该结果，该引理的`σ.Perm (List.range n)`条件可通过一次内核校验的`decide`操作得到解决。这一核心思想——将快速的不可信简化与单一的已验证重构分开——归功于Mikhalchuk、Gladshtein和Sergey。
- Charguéraud, A. (2020). “顺序程序的分离逻辑（函数式Pearl）。”*Proc. ACM Program. Lang.* 4, ICFP，文章116。
  https://doi.org/10.1145/3408998
- **bedrock2**：https://github.com/mit-plv/bedrock2
  `Tactics/XCancel.lean`和`Tactics/SeqFrame.lean`中的框架自动化策略（`xcancel`、`seqFrame`）灵感来源于bedrock2的分离逻辑自动化技术。具体而言：
  - `bedrock2/src/bedrock2/SepLogAddrArith.v`（第127-134行）中的`wcancel`策略启发了取消方法：通过标签+地址来匹配原子，并将未匹配的假设原子作为剩余部分来计算框架。
  - `bedrock2/src/bedrock2/FrameRule.v`（第75-175行）中的框架规则架构启发了自动提取框架的模式，即规范中包含一个通用框架参数，各策略在组合时会实例化该参数。
  - `compiler/src/compiler/GoFlatToRiscv.v`（第439-546行）中带有明确框架的指令规范为使用`cpsTriple_frameR` + `cpsTriple_seq_perm_same_cr`来组合指令规范的设计提供了参考。
- Knuth, D.E. (1997). *计算机程序设计艺术，第2卷：
《半数值算法》*（第3版），§4.3.1“经典算法”。Addison-Wesley出版社。在`Evm64/DivMod.lean`中，DIV/MOD操作码采用了算法D。  
- zkvm-standards：https://github.com/eth-act/zkvm-standards  
  这是针对zkVM RISC-V目标、I/O接口以及C接口加速器的标准。位于`EvmAsm/Evm64/zkvm-standards/standards/c-interface-accelerators/zkvm_accelerators.h`中的预置头文件，是经过验证的客机在进行加密预编译、KECCAK256及secp256k1验证时所依赖的标准加速器C ABI；相关决策记录、完整设计说明以及各预编译对应的映射表/EVM预编译→加速器映射表，请参见[`docs/zkvm-accelerators-interface.md`](docs/zkvm-accelerators-interface.md)。  
- 主机I/O C ABI（权威来源）：  
  `EvmAsm/Evm64/zkvm-standards/standards/io-interface/README.md`定义了标准的主机I/O接口（`read_input`/`write_output`）。决策记录、SP1版本的`HINT_LEN`/`HINT_READ`/`COMMIT`→zkvm-standards的映射关系，以及记录在beads父项目`evm-asm-96ysd`下的迁移计划（GH #114/#116），可参见[`docs/zkvm-host-io-interface.md`](docs/zkvm-host-io-interface.md)。  
- SP1 zkVM：https://github.com/succinctlabs/sp1  
  RISC-V的`ECALL`框架（指令编码、寄存器约定、通过`a0`返回）遵循SP1所采用的相同机制；函数集和参数布局则依据`zkvm_accelerators.h`，而非SP1的系统调用表。具体的系统调用编号属于主机相关细节，会在ECALL处理程序中进行重映射，并在beads父项目`evm-asm-nr2sk`中按桥接节点进行跟踪。  
- sail-riscv-lean：https://github.com/opencompl/sail-riscv-lean  
- RISC-V指令集规范：https://riscv.org/technical/specifications/
