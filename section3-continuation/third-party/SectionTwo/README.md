# IGS III — Section 2 Lean formalisation

固定版本 IGS III Section 2（Chemical geometry）及所需 Appendix A 已完成形式化。357个III模块（38,657行）全部构建通过；3,318个项目声明（含private/generated及Universality命名空间内新增者）的传递公理审计仅含Lean标准的propext、Classical.choice、Quot.sound。源码无sorry、admit或新增目标公理；审计前后源码/object SHA256一致。最终审计UTC时间2026-10-09 22:57:53，详见verification/manifest.json、status.txt、axioms.log和build.log。

统一入口是 [IGSIII/SectionTwo.lean](IGSIII/SectionTwo.lean)。仅输入Classical rule、0<p<1与reliability(p)=p，在同一λ/amplitude/field/K上给实际全簇ordered two-marked GHP、fullsupport、正terminal距离、上下box维数=logρ/logλ、全remaining-depth直径sup的所有有限阶Lp，以及可测编码。完整scalar、四活态mass Perron、intrinsic cell localisation及其条件law、等长/diamond/五环实例和附录mesh的逐条对应见 [COVERAGE.md](COVERAGE.md)。

随机compact marked metric-measure space采用忠实的可测可数编码：相同增强code给同一个保全部固定顶点labels、两个orderedterminals与实际极限measure的IsometryEquiv。没有另行实现抽象marked-GHP quotient的Borel映射库。条件独立指不同socket的联合C/N续接；同B胞两侧共享原始QN。

## 固定版本与依赖

- Overleaf III：69ea70d9bc1829f2de6e2d6d，提交f0c4804685ad6aed415ac4f69926dff71960d641（2026-10-09 23:02:14 Asia/Shanghai）。
- Lean 4.32.1；mathlib 520045ab14e26149ee970e2e617ca04b09bde5d6。
- II源码固定提交f35572fcee521d803b47cd7df74238d2ecb3582d，位于vendor/Universality，作为本地Lake依赖。来源：[GitHub](https://github.com/Nero-17/LEAN-Formalisation-IGS-Bernoulli-percolation-universality-class)。
- 连续轮开始2026-10-09 23:38:56 Asia/Shanghai；轮次2026-10-09-233856。完整过程、失败路线、精确条件与结束信息见 [RESEARCH_RECORD.md](RESEARCH_RECORD.md)。

## 复核

依赖已编译时，在PowerShell运行 ./scripts/verify.ps1，可用 -Lake 参数指定lake.exe绝对路径。脚本按imports排序编译全部III模块，检查源码及依赖对象SHA256，再编译总入口并审计全部项目声明的传递公理。只能用manifest的时间和哈希判断该次验收范围；修改源码后应重新运行。

全新环境需安装lean-toolchain列出的版本，执行lake update、lake exe cache get，并先编译vendored II依赖（直接lake build IGSIII会一并编译依赖）。本轮复用了源码逐一匹配的1130个II编译对象，复制于本工程独立缓存；没有从零重编II全库。归档包含完整固定依赖源码及许可证，不含.lake缓存。

证明中的通用条件工具均由真实模型定理实例化后才计入完成，没有把结论藏进结构字段或输入证书。scalar构造和full-mesh使用已证明的替代路线；cell-route辅助min等式未逐字单独立声明，已证明的cone/boundarysum完成全部localisation结论。实际五环严格λ>2有精确证明，十进制2.0536未数值认证。原文证明路线同步属于后续写作工作；本轮没有新增全局AO结论。
