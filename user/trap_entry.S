#include <uapi/machine/trap.h>
#include <uapi/machine/trap_support.h>

.section .text

.macro	TRAP_ENTRY nr name handler has_error_code:req
.align	2
\name:
	/* push 0 if the hardware doesn't push error code */
	.ifeq	\has_error_code
	pushq	$0
	.endif

	/* reserve space for trap_regs */
	subq	$TRAP_REGS_SIZE, %rsp
	callq	trap_common_entry
	movq	%rsp, %rdi
	addq	$TRAP_REGS_SIZE, %rdi

	/* trap number */
	movq	$\nr, %rsi

	callq	\handler
	jmp	trap_common_exit
.endm

trap_common_entry:
	SAVE_C_REGS	offset=8
	SAVE_EXTRA_REGS	offset=8
	/* prevent stack backtrace for now */
	movq	$0, %rbp
	ret

trap_common_exit:
	LOAD_EXTRA_REGS	offset=0
	LOAD_C_REGS	offset=0
	/* skip trap_regs and error code */
	addq	$TRAP_REGS_SIZE+8, %rsp
	iretq

TRAP_ENTRY	0	vector0		trap	has_error_code=0
TRAP_ENTRY	1	vector1		trap	has_error_code=0
TRAP_ENTRY	2	vector2		trap	has_error_code=0
TRAP_ENTRY	3	vector3		trap	has_error_code=0
TRAP_ENTRY	4	vector4		trap	has_error_code=0
TRAP_ENTRY	5	vector5		trap	has_error_code=0
TRAP_ENTRY	6	vector6		trap	has_error_code=0
TRAP_ENTRY	7	vector7		trap	has_error_code=0
TRAP_ENTRY	8	vector8		trap	has_error_code=1
TRAP_ENTRY	9	vector9		trap	has_error_code=0
TRAP_ENTRY	10	vector10	trap	has_error_code=1
TRAP_ENTRY	11	vector11	trap	has_error_code=1
TRAP_ENTRY	12	vector12	trap	has_error_code=1
TRAP_ENTRY	13	vector13	trap	has_error_code=1
TRAP_ENTRY	14	vector14	trap	has_error_code=1
TRAP_ENTRY	15	vector15	trap	has_error_code=0
TRAP_ENTRY	16	vector16	trap	has_error_code=0
TRAP_ENTRY	17	vector17	trap	has_error_code=1
TRAP_ENTRY	18	vector18	trap	has_error_code=0
TRAP_ENTRY	19	vector19	trap	has_error_code=0
TRAP_ENTRY	20	vector20	trap	has_error_code=0
TRAP_ENTRY	21	vector21	trap	has_error_code=0
TRAP_ENTRY	22	vector22	trap	has_error_code=0
TRAP_ENTRY	23	vector23	trap	has_error_code=0
TRAP_ENTRY	24	vector24	trap	has_error_code=0
TRAP_ENTRY	25	vector25	trap	has_error_code=0
TRAP_ENTRY	26	vector26	trap	has_error_code=0
TRAP_ENTRY	27	vector27	trap	has_error_code=0
TRAP_ENTRY	28	vector28	trap	has_error_code=0
TRAP_ENTRY	29	vector29	trap	has_error_code=0
TRAP_ENTRY	30	vector30	trap	has_error_code=0
TRAP_ENTRY	31	vector31	trap	has_error_code=0
TRAP_ENTRY	32	vector32	trap	has_error_code=0
TRAP_ENTRY	33	vector33	trap	has_error_code=0
TRAP_ENTRY	34	vector34	trap	has_error_code=0
TRAP_ENTRY	35	vector35	trap	has_error_code=0
TRAP_ENTRY	36	vector36	trap	has_error_code=0
TRAP_ENTRY	37	vector37	trap	has_error_code=0
TRAP_ENTRY	38	vector38	trap	has_error_code=0
TRAP_ENTRY	39	vector39	trap	has_error_code=0
TRAP_ENTRY	40	vector40	trap	has_error_code=0
TRAP_ENTRY	41	vector41	trap	has_error_code=0
TRAP_ENTRY	42	vector42	trap	has_error_code=0
TRAP_ENTRY	43	vector43	trap	has_error_code=0
TRAP_ENTRY	44	vector44	trap	has_error_code=0
TRAP_ENTRY	45	vector45	trap	has_error_code=0
TRAP_ENTRY	46	vector46	trap	has_error_code=0
TRAP_ENTRY	47	vector47	trap	has_error_code=0
TRAP_ENTRY	48	vector48	trap	has_error_code=0
TRAP_ENTRY	49	vector49	trap	has_error_code=0
TRAP_ENTRY	50	vector50	trap	has_error_code=0
TRAP_ENTRY	51	vector51	trap	has_error_code=0
TRAP_ENTRY	52	vector52	trap	has_error_code=0
TRAP_ENTRY	53	vector53	trap	has_error_code=0
TRAP_ENTRY	54	vector54	trap	has_error_code=0
TRAP_ENTRY	55	vector55	trap	has_error_code=0
TRAP_ENTRY	56	vector56	trap	has_error_code=0
TRAP_ENTRY	57	vector57	trap	has_error_code=0
TRAP_ENTRY	58	vector58	trap	has_error_code=0
TRAP_ENTRY	59	vector59	trap	has_error_code=0
TRAP_ENTRY	60	vector60	trap	has_error_code=0
TRAP_ENTRY	61	vector61	trap	has_error_code=0
TRAP_ENTRY	62	vector62	trap	has_error_code=0
TRAP_ENTRY	63	vector63	trap	has_error_code=0
TRAP_ENTRY	64	vector64	trap	has_error_code=0
TRAP_ENTRY	65	vector65	trap	has_error_code=0
TRAP_ENTRY	66	vector66	trap	has_error_code=0
TRAP_ENTRY	67	vector67	trap	has_error_code=0
TRAP_ENTRY	68	vector68	trap	has_error_code=0
TRAP_ENTRY	69	vector69	trap	has_error_code=0
TRAP_ENTRY	70	vector70	trap	has_error_code=0
TRAP_ENTRY	71	vector71	trap	has_error_code=0
TRAP_ENTRY	72	vector72	trap	has_error_code=0
TRAP_ENTRY	73	vector73	trap	has_error_code=0
TRAP_ENTRY	74	vector74	trap	has_error_code=0
TRAP_ENTRY	75	vector75	trap	has_error_code=0
TRAP_ENTRY	76	vector76	trap	has_error_code=0
TRAP_ENTRY	77	vector77	trap	has_error_code=0
TRAP_ENTRY	78	vector78	trap	has_error_code=0
TRAP_ENTRY	79	vector79	trap	has_error_code=0
TRAP_ENTRY	80	vector80	trap	has_error_code=0
TRAP_ENTRY	81	vector81	trap	has_error_code=0
TRAP_ENTRY	82	vector82	trap	has_error_code=0
TRAP_ENTRY	83	vector83	trap	has_error_code=0
TRAP_ENTRY	84	vector84	trap	has_error_code=0
TRAP_ENTRY	85	vector85	trap	has_error_code=0
TRAP_ENTRY	86	vector86	trap	has_error_code=0
TRAP_ENTRY	87	vector87	trap	has_error_code=0
TRAP_ENTRY	88	vector88	trap	has_error_code=0
TRAP_ENTRY	89	vector89	trap	has_error_code=0
TRAP_ENTRY	90	vector90	trap	has_error_code=0
TRAP_ENTRY	91	vector91	trap	has_error_code=0
TRAP_ENTRY	92	vector92	trap	has_error_code=0
TRAP_ENTRY	93	vector93	trap	has_error_code=0
TRAP_ENTRY	94	vector94	trap	has_error_code=0
TRAP_ENTRY	95	vector95	trap	has_error_code=0
TRAP_ENTRY	96	vector96	trap	has_error_code=0
TRAP_ENTRY	97	vector97	trap	has_error_code=0
TRAP_ENTRY	98	vector98	trap	has_error_code=0
TRAP_ENTRY	99	vector99	trap	has_error_code=0
TRAP_ENTRY	100	vector100	trap	has_error_code=0
TRAP_ENTRY	101	vector101	trap	has_error_code=0
TRAP_ENTRY	102	vector102	trap	has_error_code=0
TRAP_ENTRY	103	vector103	trap	has_error_code=0
TRAP_ENTRY	104	vector104	trap	has_error_code=0
TRAP_ENTRY	105	vector105	trap	has_error_code=0
TRAP_ENTRY	106	vector106	trap	has_error_code=0
TRAP_ENTRY	107	vector107	trap	has_error_code=0
TRAP_ENTRY	108	vector108	trap	has_error_code=0
TRAP_ENTRY	109	vector109	trap	has_error_code=0
TRAP_ENTRY	110	vector110	trap	has_error_code=0
TRAP_ENTRY	111	vector111	trap	has_error_code=0
TRAP_ENTRY	112	vector112	trap	has_error_code=0
TRAP_ENTRY	113	vector113	trap	has_error_code=0
TRAP_ENTRY	114	vector114	trap	has_error_code=0
TRAP_ENTRY	115	vector115	trap	has_error_code=0
TRAP_ENTRY	116	vector116	trap	has_error_code=0
TRAP_ENTRY	117	vector117	trap	has_error_code=0
TRAP_ENTRY	118	vector118	trap	has_error_code=0
TRAP_ENTRY	119	vector119	trap	has_error_code=0
TRAP_ENTRY	120	vector120	trap	has_error_code=0
TRAP_ENTRY	121	vector121	trap	has_error_code=0
TRAP_ENTRY	122	vector122	trap	has_error_code=0
TRAP_ENTRY	123	vector123	trap	has_error_code=0
TRAP_ENTRY	124	vector124	trap	has_error_code=0
TRAP_ENTRY	125	vector125	trap	has_error_code=0
TRAP_ENTRY	126	vector126	trap	has_error_code=0
TRAP_ENTRY	127	vector127	trap	has_error_code=0
TRAP_ENTRY	128	vector128	trap	has_error_code=0
TRAP_ENTRY	129	vector129	trap	has_error_code=0
TRAP_ENTRY	130	vector130	trap	has_error_code=0
TRAP_ENTRY	131	vector131	trap	has_error_code=0
TRAP_ENTRY	132	vector132	trap	has_error_code=0
TRAP_ENTRY	133	vector133	trap	has_error_code=0
TRAP_ENTRY	134	vector134	trap	has_error_code=0
TRAP_ENTRY	135	vector135	trap	has_error_code=0
TRAP_ENTRY	136	vector136	trap	has_error_code=0
TRAP_ENTRY	137	vector137	trap	has_error_code=0
TRAP_ENTRY	138	vector138	trap	has_error_code=0
TRAP_ENTRY	139	vector139	trap	has_error_code=0
TRAP_ENTRY	140	vector140	trap	has_error_code=0
TRAP_ENTRY	141	vector141	trap	has_error_code=0
TRAP_ENTRY	142	vector142	trap	has_error_code=0
TRAP_ENTRY	143	vector143	trap	has_error_code=0
TRAP_ENTRY	144	vector144	trap	has_error_code=0
TRAP_ENTRY	145	vector145	trap	has_error_code=0
TRAP_ENTRY	146	vector146	trap	has_error_code=0
TRAP_ENTRY	147	vector147	trap	has_error_code=0
TRAP_ENTRY	148	vector148	trap	has_error_code=0
TRAP_ENTRY	149	vector149	trap	has_error_code=0
TRAP_ENTRY	150	vector150	trap	has_error_code=0
TRAP_ENTRY	151	vector151	trap	has_error_code=0
TRAP_ENTRY	152	vector152	trap	has_error_code=0
TRAP_ENTRY	153	vector153	trap	has_error_code=0
TRAP_ENTRY	154	vector154	trap	has_error_code=0
TRAP_ENTRY	155	vector155	trap	has_error_code=0
TRAP_ENTRY	156	vector156	trap	has_error_code=0
TRAP_ENTRY	157	vector157	trap	has_error_code=0
TRAP_ENTRY	158	vector158	trap	has_error_code=0
TRAP_ENTRY	159	vector159	trap	has_error_code=0
TRAP_ENTRY	160	vector160	trap	has_error_code=0
TRAP_ENTRY	161	vector161	trap	has_error_code=0
TRAP_ENTRY	162	vector162	trap	has_error_code=0
TRAP_ENTRY	163	vector163	trap	has_error_code=0
TRAP_ENTRY	164	vector164	trap	has_error_code=0
TRAP_ENTRY	165	vector165	trap	has_error_code=0
TRAP_ENTRY	166	vector166	trap	has_error_code=0
TRAP_ENTRY	167	vector167	trap	has_error_code=0
TRAP_ENTRY	168	vector168	trap	has_error_code=0
TRAP_ENTRY	169	vector169	trap	has_error_code=0
TRAP_ENTRY	170	vector170	trap	has_error_code=0
TRAP_ENTRY	171	vector171	trap	has_error_code=0
TRAP_ENTRY	172	vector172	trap	has_error_code=0
TRAP_ENTRY	173	vector173	trap	has_error_code=0
TRAP_ENTRY	174	vector174	trap	has_error_code=0
TRAP_ENTRY	175	vector175	trap	has_error_code=0
TRAP_ENTRY	176	vector176	trap	has_error_code=0
TRAP_ENTRY	177	vector177	trap	has_error_code=0
TRAP_ENTRY	178	vector178	trap	has_error_code=0
TRAP_ENTRY	179	vector179	trap	has_error_code=0
TRAP_ENTRY	180	vector180	trap	has_error_code=0
TRAP_ENTRY	181	vector181	trap	has_error_code=0
TRAP_ENTRY	182	vector182	trap	has_error_code=0
TRAP_ENTRY	183	vector183	trap	has_error_code=0
TRAP_ENTRY	184	vector184	trap	has_error_code=0
TRAP_ENTRY	185	vector185	trap	has_error_code=0
TRAP_ENTRY	186	vector186	trap	has_error_code=0
TRAP_ENTRY	187	vector187	trap	has_error_code=0
TRAP_ENTRY	188	vector188	trap	has_error_code=0
TRAP_ENTRY	189	vector189	trap	has_error_code=0
TRAP_ENTRY	190	vector190	trap	has_error_code=0
TRAP_ENTRY	191	vector191	trap	has_error_code=0
TRAP_ENTRY	192	vector192	trap	has_error_code=0
TRAP_ENTRY	193	vector193	trap	has_error_code=0
TRAP_ENTRY	194	vector194	trap	has_error_code=0
TRAP_ENTRY	195	vector195	trap	has_error_code=0
TRAP_ENTRY	196	vector196	trap	has_error_code=0
TRAP_ENTRY	197	vector197	trap	has_error_code=0
TRAP_ENTRY	198	vector198	trap	has_error_code=0
TRAP_ENTRY	199	vector199	trap	has_error_code=0
TRAP_ENTRY	200	vector200	trap	has_error_code=0
TRAP_ENTRY	201	vector201	trap	has_error_code=0
TRAP_ENTRY	202	vector202	trap	has_error_code=0
TRAP_ENTRY	203	vector203	trap	has_error_code=0
TRAP_ENTRY	204	vector204	trap	has_error_code=0
TRAP_ENTRY	205	vector205	trap	has_error_code=0
TRAP_ENTRY	206	vector206	trap	has_error_code=0
TRAP_ENTRY	207	vector207	trap	has_error_code=0
TRAP_ENTRY	208	vector208	trap	has_error_code=0
TRAP_ENTRY	209	vector209	trap	has_error_code=0
TRAP_ENTRY	210	vector210	trap	has_error_code=0
TRAP_ENTRY	211	vector211	trap	has_error_code=0
TRAP_ENTRY	212	vector212	trap	has_error_code=0
TRAP_ENTRY	213	vector213	trap	has_error_code=0
TRAP_ENTRY	214	vector214	trap	has_error_code=0
TRAP_ENTRY	215	vector215	trap	has_error_code=0
TRAP_ENTRY	216	vector216	trap	has_error_code=0
TRAP_ENTRY	217	vector217	trap	has_error_code=0
TRAP_ENTRY	218	vector218	trap	has_error_code=0
TRAP_ENTRY	219	vector219	trap	has_error_code=0
TRAP_ENTRY	220	vector220	trap	has_error_code=0
TRAP_ENTRY	221	vector221	trap	has_error_code=0
TRAP_ENTRY	222	vector222	trap	has_error_code=0
TRAP_ENTRY	223	vector223	trap	has_error_code=0
TRAP_ENTRY	224	vector224	trap	has_error_code=0
TRAP_ENTRY	225	vector225	trap	has_error_code=0
TRAP_ENTRY	226	vector226	trap	has_error_code=0
TRAP_ENTRY	227	vector227	trap	has_error_code=0
TRAP_ENTRY	228	vector228	trap	has_error_code=0
TRAP_ENTRY	229	vector229	trap	has_error_code=0
TRAP_ENTRY	230	vector230	trap	has_error_code=0
TRAP_ENTRY	231	vector231	trap	has_error_code=0
TRAP_ENTRY	232	vector232	trap	has_error_code=0
TRAP_ENTRY	233	vector233	trap	has_error_code=0
TRAP_ENTRY	234	vector234	trap	has_error_code=0
TRAP_ENTRY	235	vector235	trap	has_error_code=0
TRAP_ENTRY	236	vector236	trap	has_error_code=0
TRAP_ENTRY	237	vector237	trap	has_error_code=0
TRAP_ENTRY	238	vector238	trap	has_error_code=0
TRAP_ENTRY	239	vector239	trap	has_error_code=0
TRAP_ENTRY	240	vector240	trap	has_error_code=0
TRAP_ENTRY	241	vector241	trap	has_error_code=0
TRAP_ENTRY	242	vector242	trap	has_error_code=0
TRAP_ENTRY	243	vector243	trap	has_error_code=0
TRAP_ENTRY	244	vector244	trap	has_error_code=0
TRAP_ENTRY	245	vector245	trap	has_error_code=0
TRAP_ENTRY	246	vector246	trap	has_error_code=0
TRAP_ENTRY	247	vector247	trap	has_error_code=0
TRAP_ENTRY	248	vector248	trap	has_error_code=0
TRAP_ENTRY	249	vector249	trap	has_error_code=0
TRAP_ENTRY	250	vector250	trap	has_error_code=0
TRAP_ENTRY	251	vector251	trap	has_error_code=0
TRAP_ENTRY	252	vector252	trap	has_error_code=0
TRAP_ENTRY	253	vector253	trap	has_error_code=0
TRAP_ENTRY	254	vector254	trap	has_error_code=0
TRAP_ENTRY	255	vector255	trap	has_error_code=0

.section .data
.global	trap_vectors
trap_vectors:
	.quad	vector0
	.quad	vector1
	.quad	vector2
	.quad	vector3
	.quad	vector4
	.quad	vector5
	.quad	vector6
	.quad	vector7
	.quad	vector8
	.quad	vector9
	.quad	vector10
	.quad	vector11
	.quad	vector12
	.quad	vector13
	.quad	vector14
	.quad	vector15
	.quad	vector16
	.quad	vector17
	.quad	vector18
	.quad	vector19
	.quad	vector20
	.quad	vector21
	.quad	vector22
	.quad	vector23
	.quad	vector24
	.quad	vector25
	.quad	vector26
	.quad	vector27
	.quad	vector28
	.quad	vector29
	.quad	vector30
	.quad	vector31
	.quad	vector32
	.quad	vector33
	.quad	vector34
	.quad	vector35
	.quad	vector36
	.quad	vector37
	.quad	vector38
	.quad	vector39
	.quad	vector40
	.quad	vector41
	.quad	vector42
	.quad	vector43
	.quad	vector44
	.quad	vector45
	.quad	vector46
	.quad	vector47
	.quad	vector48
	.quad	vector49
	.quad	vector50
	.quad	vector51
	.quad	vector52
	.quad	vector53
	.quad	vector54
	.quad	vector55
	.quad	vector56
	.quad	vector57
	.quad	vector58
	.quad	vector59
	.quad	vector60
	.quad	vector61
	.quad	vector62
	.quad	vector63
	.quad	vector64
	.quad	vector65
	.quad	vector66
	.quad	vector67
	.quad	vector68
	.quad	vector69
	.quad	vector70
	.quad	vector71
	.quad	vector72
	.quad	vector73
	.quad	vector74
	.quad	vector75
	.quad	vector76
	.quad	vector77
	.quad	vector78
	.quad	vector79
	.quad	vector80
	.quad	vector81
	.quad	vector82
	.quad	vector83
	.quad	vector84
	.quad	vector85
	.quad	vector86
	.quad	vector87
	.quad	vector88
	.quad	vector89
	.quad	vector90
	.quad	vector91
	.quad	vector92
	.quad	vector93
	.quad	vector94
	.quad	vector95
	.quad	vector96
	.quad	vector97
	.quad	vector98
	.quad	vector99
	.quad	vector100
	.quad	vector101
	.quad	vector102
	.quad	vector103
	.quad	vector104
	.quad	vector105
	.quad	vector106
	.quad	vector107
	.quad	vector108
	.quad	vector109
	.quad	vector110
	.quad	vector111
	.quad	vector112
	.quad	vector113
	.quad	vector114
	.quad	vector115
	.quad	vector116
	.quad	vector117
	.quad	vector118
	.quad	vector119
	.quad	vector120
	.quad	vector121
	.quad	vector122
	.quad	vector123
	.quad	vector124
	.quad	vector125
	.quad	vector126
	.quad	vector127
	.quad	vector128
	.quad	vector129
	.quad	vector130
	.quad	vector131
	.quad	vector132
	.quad	vector133
	.quad	vector134
	.quad	vector135
	.quad	vector136
	.quad	vector137
	.quad	vector138
	.quad	vector139
	.quad	vector140
	.quad	vector141
	.quad	vector142
	.quad	vector143
	.quad	vector144
	.quad	vector145
	.quad	vector146
	.quad	vector147
	.quad	vector148
	.quad	vector149
	.quad	vector150
	.quad	vector151
	.quad	vector152
	.quad	vector153
	.quad	vector154
	.quad	vector155
	.quad	vector156
	.quad	vector157
	.quad	vector158
	.quad	vector159
	.quad	vector160
	.quad	vector161
	.quad	vector162
	.quad	vector163
	.quad	vector164
	.quad	vector165
	.quad	vector166
	.quad	vector167
	.quad	vector168
	.quad	vector169
	.quad	vector170
	.quad	vector171
	.quad	vector172
	.quad	vector173
	.quad	vector174
	.quad	vector175
	.quad	vector176
	.quad	vector177
	.quad	vector178
	.quad	vector179
	.quad	vector180
	.quad	vector181
	.quad	vector182
	.quad	vector183
	.quad	vector184
	.quad	vector185
	.quad	vector186
	.quad	vector187
	.quad	vector188
	.quad	vector189
	.quad	vector190
	.quad	vector191
	.quad	vector192
	.quad	vector193
	.quad	vector194
	.quad	vector195
	.quad	vector196
	.quad	vector197
	.quad	vector198
	.quad	vector199
	.quad	vector200
	.quad	vector201
	.quad	vector202
	.quad	vector203
	.quad	vector204
	.quad	vector205
	.quad	vector206
	.quad	vector207
	.quad	vector208
	.quad	vector209
	.quad	vector210
	.quad	vector211
	.quad	vector212
	.quad	vector213
	.quad	vector214
	.quad	vector215
	.quad	vector216
	.quad	vector217
	.quad	vector218
	.quad	vector219
	.quad	vector220
	.quad	vector221
	.quad	vector222
	.quad	vector223
	.quad	vector224
	.quad	vector225
	.quad	vector226
	.quad	vector227
	.quad	vector228
	.quad	vector229
	.quad	vector230
	.quad	vector231
	.quad	vector232
	.quad	vector233
	.quad	vector234
	.quad	vector235
	.quad	vector236
	.quad	vector237
	.quad	vector238
	.quad	vector239
	.quad	vector240
	.quad	vector241
	.quad	vector242
	.quad	vector243
	.quad	vector244
	.quad	vector245
	.quad	vector246
	.quad	vector247
	.quad	vector248
	.quad	vector249
	.quad	vector250
	.quad	vector251
	.quad	vector252
	.quad	vector253
	.quad	vector254
	.quad	vector255
