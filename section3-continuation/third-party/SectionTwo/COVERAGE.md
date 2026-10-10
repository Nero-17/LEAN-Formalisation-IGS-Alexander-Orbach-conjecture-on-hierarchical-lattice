# Section 2 与附录 A 的形式化覆盖

来源固定为 Overleaf III `f0c4804685ad6aed415ac4f69926dff71960d641`，Section 2（Chemical geometry）及 Appendix A（chemical scalar / full mesh）。这里按原文标签列对应结果；通用条件工具不单独计作原文结论完成。最终验收已于2026-10-10 06:57:53 Asia/Shanghai通过：357个III模块（38,657行）全部构建，3,318个项目声明的传递公理仅含propext/Classical.choice/Quot.sound；审计前后源码/object哈希一致。证据见verification/manifest.json、build.log、axioms.log与status.txt。

| 原文标签 / 内容 | 真实模型的形式化入口 | 当前状态 |
|---|---|---|
| critical-cluster、创新树与 scalar 递归 | `Chemical/SubstitutionPaths/FullRecursion`、`Generation`、`MarkedConfigurationLaw`、`InnovationCylinders` | 完成。实际全簇与 II conditioned law 相同；任意 noncrossing dangling fragments 均保留；首张 rule 图对应原文 depth 1，`FiniteDepthIndexing` 单独含 depth 0 |
| shortest-path functional 的性质、增长界 | `Chemical/PathFunctional` 及 `Chemical/SubstitutionPaths` 的 finite graph、path projection、weighted leaf law | 完成。真实加权图距离、simple paths、单调/凹/齐次/超可加/L1 Lipschitz、微观路径递归 |
| chemical-scalar | `Chemical/ChemicalScalar.exists_actual_chemical_scalar` | 完成。只输入 Classical rule 与内部固定点；同一实际概率空间上 λ∈[ell,L]、正mean-one内生场、amplitude≥1、全部地址整列 AE/所有有限正阶Lp、均值比值极限、stationarity、正负全部矩与任意正参数指数矩 |
| chemical-scales：等长与diamond | `Chemical/EqualLengthScalar.exists_actual_equal_length_scalar`、`Chemical/SmallBall/DiamondScalar` | 完成。实际所有 crossing 图的 terminal distance 精确为 ell^n；同 scalar witness 的 λ=ell、amplitude=1、field=1；standard diamond λ=2 |
| chemical-scales：五环 | `Chemical/SubstitutionPaths/FiveCycleGrowth`、`FiveCycleBranchLaw`、`FiveCycleInverseMoments` | 完成。实际 Classical 五环、critical polynomial、条件两弧 law、逆三阶递推与显式同λ下界；严格 λ>2 不依赖数值近似 |
| mass-perron | `Mass/FourStateMassPerron.Classical.four_state_mass_perron`、`FourStateMassLimit.Classical.four_state_mass_limit` | 完成。真实四活态 M^4>0、ρ≥ell、正左右向量与归一化、所有population坐标同 W、EW=1、W>0 a.s.、真实顶点birth reward与κ公式 |
| mass-perron：component cylinders、B两侧 | `Mass/ComponentCylinderWeights`、`ComponentBoundaryLaw`、`ComponentFinitePartition`、`FullComponentEmpiricalWeights` | 完成。所有固定component词真实计数比值/一致性/connected正性；两侧B用原始联合marks；全簇概率权含2个terminal及frontier残余，残余趋零 |
| full-ghp：实际空间与ordered marks | `Chemical/SmallBall/ActualChemicalMarkedGH`、`Geometry/CriticalChemicalGH`、`ActualClusterGromovHausdorff` | 完成实际全簇 marked GH、紧completion、正terminal距离。有限/极限 skeleton 按真实同一顶点标签匹配 |
| full-ghp：概率测度与full support | `Geometry/CriticalComponentBoundary.exists_actual_critical_component_boundary` | 完成。同一实际 K 的真实概率边界 law、Borel realization pushforward、实际圆柱质量及投影Prokhorov收敛、全支撑 |
| full-ghp：全顶点uniformμ、two-marked GHP | `Geometry/ActualFullComponentOwnership`、`FullComponentMassApproximation`、`MarkedGromovHausdorffProkhorov`；`Geometry/CriticalComponentGHP.exists_actual_critical_component_marked_ghp` | 完成。只Classical+critical输入；真正同一共同metric控制Hausdorff、全顶点均匀概率的Prokhorov及原orderedmarks，完整whole-sequence实际化 |
| cell-localisation：真实intrinsic completion | `Geometry/RootedComponentSkeleton`、`Persistence`、`Anchors`、`GenericComponentLengths`、`Compactness`、`ActualCellLocalisation` | 完成真实component内在路径metric、全局归一化、available planted boundaries、紧completion、实际canonical inclusion 1-Lipschitz/单射/closed embedding |
| cell-localisation：边界分离/交集 | `Geometry/CellLocalisationIntersection`、`CellLocalisationSplitIntersection` | 完成。异edge两component与同QN edge两侧均有intrinsic boundary-radius sum距离下界，交集只能是可用的公共planted vertex；没有人工连接B两侧 |
| cell-localisation：缩放与条件law | `Geometry/CellLocalisationCriticalLaw.exists_actual_critical_completed_cell_family`、`CellLocalisationShiftedCompletion`、`CellLocalisationMarkedCompletionLaw` | 已完成实际 GH-valued completion family、全点距离精确缩放、joint four-branch family×全部标签metriccode的共同frontier积law及whole-prefix独立性；`CellLocalisationActualSimilarity` 已直接给actual blockcell与shifted root completion的精确相似同构并保留全部vertex/terminal标签 |
| cell-localisation：正内半径 | `Geometry/RootedComponentInterior.rootedComponentSpace_positive_interior_radius`、`Chemical/SmallBall/PositiveFieldGoodEvent` | 完成。真实第一crossing path内部顶点的正边界距离；从AE正性得到确定正阈值及正概率，不假设统一正下界 |
| 随机空间可测表示与忠实性 | `Geometry/ChemicalMeasureCodeFaithfulness.chemicalMarkedMetricMeasureCode_measurable`、`exists_actual_marked_measure_isometryEquiv_of_code_eq` | 完成。实际可数编码可测，相同编码给保全部labels、两个orderedmarks及实际极限measure的同一个IsometryEquiv；采用忠实编码表示 |
| 同一witness统一入口 | `SectionTwo.exists_actual_critical_section_two_geometry` | 完成并纳入最终稳定审计。上述GHP、fullsupport、正terminal距离、上下box维数等式、全depth直径矩与基础/增强可测编码使用相同λ/field/K，圆柱mass code精确等于countlimit |
| chemical-dimension | `Geometry/BoxDimensionDefinition`、`BoxDimensionLowerDefinition` | 完成按最小球覆盖数定义的上下box维数，允许无限覆盖数且证明相关极限顺序 |
| chemical-box-dimension | `Geometry/BoxDimensionCriticalEquality`、`BoxDimensionSameWitness.actual_critical_box_dimension_of_mean_bounds_and_positive_field` | 完成。Classical/critical实际模型上下box维数=logρ/logλ；可直接用于GHP同一λ、field、K。实际全部半径cover/packing及插值均已构造 |
| chemical 与 ambient exponent 比较 | `Geometry/ChemicalDimensionComparison` | 完成。由同λ≥ell得不大于ambient expected mass exponent，λ>ell时严格；五环实际λ可实例化。不声称ambient Hausdorff维数等于expected mass exponent |
| Appendix chemical-moments | `Chemical/SmallBall/FiniteDepthIndexing`、`FiniteDepthScaledMoments`、`ChemicalScalar` 的依赖链 | 完成。D_n/a_n包括seed的统一正/负全矩、阶乘界与全部正参数指数矩；实际stationary/endogenous law同样全部矩 |
| Appendix chemical-paths | `Chemical/SubstitutionPaths/PathProjection` 与 `Chemical/SmallBall` 的 paired path/barrier 模块 | 完成真实递归路径计数、单边及保留within-pair coupling的signed路径障碍；未假设sibling types独立 |
| Appendix chemical-compactness | `Chemical/SubstitutionPaths/CommonPrefixL2`、`CompactChemicalFamily` 与 `Chemical/SmallBall` 内生场/紧性模块 | 完成同一innovation概率空间的L2紧性、内生性、终端orbit共同Lp dominator及a.s.比较 |
| Appendix chemical-endpoint | `Chemical/SmallBall` 的 actual endpoint、Laplace/invariant gap 与 `Chemical/ChemicalScalar` | 完成实际omega-limit标量端点及whole-sequence提升，非输入目标证书 |
| Appendix full-mesh：all-depth supremum 的矩 | `Geometry/ComponentDiameterSupremumMoments.actual_critical_component_diameter_supremum_moments_of_mean_bounds` | 完成。真正planted component直径先对所有剩余深度取sup，再证明全部有限阶Lp；同时处理所有地址、C/N与两侧；λ由增长唯一性与主定理相同 |
| Appendix full-mesh：所有generation/depth统一指数mesh | `Geometry/FullComponentMesh.exists_actual_critical_full_component_mesh` | 完成。只Classical/critical输入，包含上一行矩断言及同AE事件上全部地址/剩余深度的真实直径指数bound。原文的无边seed通过明确depth位移处理 |

## 实际化与随机空间的表示

全簇以实际保留顶点的有限图距离、persistent skeleton、DirectLimit 和 Completion 构造。内在cell亦从实际内部路径构造，不能用ambient距离限制代替。随机完成空间使用可测GH类及完整可数标签metriccode；`ChemicalMetricMeasureCode` 增加全部真实质量圆柱的可测canonical limsup，并在已证明计数极限事件上精确识别权重。GH类单独忘记标签，标签及两端点由joint code保留。GHP收敛使用同一个真正共同metric同时比较Hausdorff、Lévy–Prokhorov和Bool ordered terminal marks。

## 与原文证明路线的差异

形式化可以采用已证明的替代论证：scalar field/endpoint依赖链与原文Schauder叙述不逐行相同；full-mesh矩使用带几何权的可数ℓ^q envelope和真实radius递推，比只用最终AE指数mesh更强。两处都证明原陈述的实际模型结论，未修改原文tex。原文与Lean的证明路线同步属于后续写作工作。

## II 复用与验收

II 固定源码 `f35572fcee521d803b47cd7df74238d2ecb3582d` 是本地依赖；有限网络、Classical rule、oriented states、critical history、population martingales、二阶vertex mass等均复用并在本工程实际对象上衔接。II ambient几何极限不能替代III chemical几何。

逐模块 EXIT0 是开发证据；最终验收必须以当前全部源码稳定的 `verification/manifest.json`、`build.log`、`axioms.log`、`status.txt` 为准。全环境审计覆盖III模块导出的全部声明和private/generated声明（含在Universality命名空间内新增者），只允许 `propext`、`Classical.choice`、`Quot.sound`。不接受 `sorry`、`admit`、`sorryAx` 或新增目标公理。


## 随机编码的最终实际化

`Chemical/SmallBall/CodedMetricMeasureUniqueness` 已整文件EXIT0：共同稠密标签距离决定complete metric realization；等距同构下两组真实原子测度相同且各自Prokhorov趋于极限，则同构保持极限measure及指定marks。`Geometry/ChemicalMetricCodeFaithfulness` 在真实模型上构造固定总原顶点标签、证明denseRange与跨层距离识别，从相同完整metriccode推出保全部labels的实际完成空间IsometryEquiv。

`Geometry/ChemicalMeasureCodeFaithfulness` 已整文件EXIT0：`chemicalMarkedMetricMeasureCode_measurable` 证明全配置/距离/cylinder mass加真实raw component-anchor标签的增强code可测；`exists_actual_marked_measure_isometryEquiv_of_code_eq` 从相同增强code直接得到保全部固定labels、两个orderedterminals和实际boundary pushforward概率的同一个IsometryEquiv。实际anchor身份来自retained vertex桥，measure身份来自真实countlimit圆柱、atomic marginal精确识别及已证明的projection Prokhorov极限。其输入的countlimit、boundary概率与atoms、Borel realization、projection convergence全部已经由CriticalComponentGHP/SectionTwo在同AE事件构造，没有额外未证明目标假设。

这是忠实的可测可数编码随机空间表示。固定sample内的Borel realization与marks→code的可测性分别证明；没有宣称实现抽象markedGHP quotient的Borel映射库。SectionTwo统一入口显式包含相同λ/amplitude/field的增强code Measurable。
独立核查说明：原证明中完整cell-route辅助min等式未逐字另立声明；已证cone、boundarysum与completion连续性足以证明cell-localisation全部结论。条件独立指不同socket的joint C/N continuations，同一B两侧保持共享QN。五环证明给精确inverse-cube下界和严格>2，未认证十进制2.0536。


