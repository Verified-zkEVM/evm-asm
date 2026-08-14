/-
  EvmAsm.Codegen.Programs.Bls12Map

  The EIP-2537 BLS12-381 map precompiles: `zkvm_bls12_map_fp_to_g1`
  (0x10) and `zkvm_bls12_map_fp2_to_g2` (0x11), mirroring
  execution-specs which delegates to py_ecc `map_to_curve_G1/G2` +
  `clear_cofactor_G1/G2`:

    SSWU onto the isogenous curve (optimized_swu_G1 / _G2, from
    eprint 2019/403) -> 11- and 3-isogeny map (Horner over the baked
    ISO_MAP coefficient tables) -> projective-to-affine (one Fermat
    inverse) -> cofactor clearing by the h_eff scalar mul through the
    EXISTING accelerated affine ops (blsg_scalar_mul / blsg2_scalar_mul).

    All Fp work runs on the Arith384Mod-backed `blsg2_fp_mul/add`
    (d = a*b + c is read-then-write, so in-place squaring is safe);
    Fp2 work on the single-syscall complex accelerators. The two big
    Fermat-style exponents (sqrt divisions) are baked LE constants:
    (p-3)/4 (top bit 378) and (p^2-9)/16 (top bit 757). sgn0 follows
    RFC 9380 (FQ: n mod 2; FQ2: sgn0(c0) or (c0 == 0 and sgn0(c1))).

  Wire format: 0x10 takes exactly one 64-byte padded Fp element, 0x11
  exactly one 128-byte padded Fp2 element; a nonzero 16-byte pad or a
  value >= p is InvalidParameter (kernel status 1 -> the dispatcher
  burns the child allotment).

  All labels are `blm_`/`blm2_`-prefixed; constants generated from
  py_ecc.optimized_bls12_381.constants verbatim.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.Bls12G2
import EvmAsm.Codegen.Programs.Bls12MapG1Real
import EvmAsm.Codegen.Programs.Bls12MapG2Real

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- Map-precompile data labels WITHOUT a `.section .data` header. -/
def bls12MapDataFragment : String :=
  ".balign 8\n" ++
  -- h_eff cofactor scalars (big-endian, for the blsg*/blsg2 scalar muls)
  "blm_heff_g1_be:\n" ++
  "  .byte 0xd2,0x01,0x00,0x00,0x00,0x01,0x00,0x01\n" ++
  "blm_heff_g2_be:\n" ++
  "  .byte 0x0b,0xc6,0x9f,0x08,0xf2,0xee,0x75,0xb3,0x58,0x4c,0x6a,0x0e,0xa9,0x1b,0x35,0x28\n" ++
  "  .byte 0x88,0xe2,0xa8,0xe9,0x14,0x5a,0xd7,0x68,0x99,0x86,0xff,0x03,0x15,0x08,0xff,0xe1\n" ++
  "  .byte 0x32,0x9c,0x2f,0x17,0x87,0x31,0xdb,0x95,0x6d,0x82,0xbf,0x01,0x5d,0x12,0x12,0xb0\n" ++
  "  .byte 0x2e,0xc0,0xec,0x69,0xd7,0x47,0x7c,0x1a,0xe9,0x54,0xcb,0xc0,0x66,0x89,0xf6,0xa3\n" ++
  "  .byte 0x59,0x89,0x4c,0x0a,0xde,0xbb,0xf6,0xb4,0xe8,0x02,0x00,0x05,0xaa,0xa9,0x55,0x51\n" ++
  -- Fp working cells (48 B LE)
  ".balign 8\n" ++
  "blm_t:\n  .zero 48\n" ++
  "blm_t2:\n  .zero 48\n" ++
  "blm_zt2:\n  .zero 48\n" ++
  "blm_tmp:\n  .zero 48\n" ++
  "blm_n:\n  .zero 48\n" ++
  "blm_d:\n  .zero 48\n" ++
  "blm_v:\n  .zero 48\n" ++
  "blm_u:\n  .zero 48\n" ++
  "blm_w:\n  .zero 48\n" ++
  "blm_r:\n  .zero 48\n" ++
  "blm_chk:\n  .zero 48\n" ++
  "blm_y:\n  .zero 48\n" ++
  "blm_s1:\n  .zero 48\n" ++
  "blm_xg:\n  .zero 48\n" ++
  "blm_yg:\n  .zero 48\n" ++
  "blm_zg:\n  .zero 48\n" ++
  "blm_zinv:\n  .zero 48\n" ++
  "blm_powt:\n  .zero 48\n" ++
  "blm_zp0:\n  .zero 48\n" ++
  "blm_zp1:\n  .zero 48\n" ++
  "blm_zp2:\n  .zero 48\n" ++
  "blm_zp3:\n  .zero 48\n" ++
  "blm_zp4:\n  .zero 48\n" ++
  "blm_zp5:\n  .zero 48\n" ++
  "blm_zp6:\n  .zero 48\n" ++
  "blm_zp7:\n  .zero 48\n" ++
  "blm_zp8:\n  .zero 48\n" ++
  "blm_zp9:\n  .zero 48\n" ++
  "blm_zp10:\n  .zero 48\n" ++
  "blm_zp11:\n  .zero 48\n" ++
  "blm_zp12:\n  .zero 48\n" ++
  "blm_zp13:\n  .zero 48\n" ++
  "blm_zp14:\n  .zero 48\n" ++
  "blm_m0:\n  .zero 48\n" ++
  "blm_m1:\n  .zero 48\n" ++
  "blm_m2:\n  .zero 48\n" ++
  "blm_m3:\n  .zero 48\n" ++
  -- Fp2 working cells (96 B LE)
  "blm2_t:\n  .zero 96\n" ++
  "blm2_t2:\n  .zero 96\n" ++
  "blm2_zt2:\n  .zero 96\n" ++
  "blm2_tmp:\n  .zero 96\n" ++
  "blm2_n:\n  .zero 96\n" ++
  "blm2_d:\n  .zero 96\n" ++
  "blm2_v:\n  .zero 96\n" ++
  "blm2_u:\n  .zero 96\n" ++
  "blm2_w:\n  .zero 96\n" ++
  "blm2_g:\n  .zero 96\n" ++
  "blm2_r:\n  .zero 96\n" ++
  "blm2_cand:\n  .zero 96\n" ++
  "blm2_chk:\n  .zero 96\n" ++
  "blm2_y:\n  .zero 96\n" ++
  "blm2_s1:\n  .zero 96\n" ++
  "blm2_s2:\n  .zero 96\n" ++
  "blm2_zp1:\n  .zero 96\n" ++
  "blm2_zp2:\n  .zero 96\n" ++
  "blm2_zp3:\n  .zero 96\n" ++
  "blm2_m0:\n  .zero 96\n" ++
  "blm2_m1:\n  .zero 96\n" ++
  "blm2_m2:\n  .zero 96\n" ++
  "blm2_m3:\n  .zero 96\n" ++
  "blm2_xg:\n  .zero 96\n" ++
  "blm2_yg:\n  .zero 96\n" ++
  "blm2_zg:\n  .zero 96\n" ++
  "blm2_zinv:\n  .zero 96\n" ++
  "blm2_powt:\n  .zero 96\n" ++
  -- affine staging: G1 compact BE 96, G2 LE point 192 + result 192
  "blm_aff:\n  .zero 96\n" ++
  "blm2_aff:\n  .zero 192\n" ++
  "blm2_res:\n  .zero 192\n" ++
  -- SSWU / isogeny constants (py_ecc optimized_bls12_381.constants)
  "blm_iso11_a:\n" ++
  "  .quad 0x5CF428082D584C1D, 0x98936F8DA0E0F97F, 0xD8E8981AEFD881AC\n" ++
  "  .quad 0xB0EA985383EE66A8, 0x3D693A02C96D4982, 0x00144698A3B8E943\n" ++
  "blm_iso11_b:\n" ++
  "  .quad 0xD1CC48E98E172BE0, 0x5A23215A316CEAA5, 0xA0B9C14FCEF35EF5\n" ++
  "  .quad 0x2016C1F0F24F4070, 0x018B12E8753EEE3B, 0x12E2908D11688030\n" ++
  "blm_iso11_z:\n" ++
  "  .quad 0x000000000000000B, 0x0000000000000000, 0x0000000000000000\n" ++
  "  .quad 0x0000000000000000, 0x0000000000000000, 0x0000000000000000\n" ++
  "blm_sqrt_m11c:\n" ++
  "  .quad 0x6F2DBEABC2BAEFF5, 0x8A407C9C6DB195E0, 0x77AE83EAB1EA8B8B\n" ++
  "  .quad 0x6B4C80EDA6FC10CE, 0xF9F2BEC613031680, 0x03D689D1E0E762CE\n" ++
  "blm_pm3d4:\n" ++
  "  .quad 0xEE7FBFFFFFFFEAAA, 0x07AAFFFFAC54FFFF, 0xD9CC34A83DAC3D89\n" ++
  "  .quad 0xD91DD2E13CE144AF, 0x92C6E9ED90D2EB35, 0x0680447A8E5FF9A6\n" ++
  "blm_k11_0_0:\n" ++
  "  .quad 0xAEAC1662734649B7, 0x5610C2D5F2E62D6E, 0xF2627B56CDB4E2C8\n" ++
  "  .quad 0x6B303E88A2D7005F, 0xB809101DD9981585, 0x11A05F2B1E833340\n" ++
  "blm_k11_0_1:\n" ++
  "  .quad 0xE834EEF1B3CB83BB, 0x4838F2A6F318C356, 0xF565E33C70D1E86B\n" ++
  "  .quad 0x7C17E75B2F6A8417, 0x0588BAB22147A81C, 0x17294ED3E943AB2F\n" ++
  "blm_k11_0_2:\n" ++
  "  .quad 0xE0179F9DAC9EDCB0, 0x958C3E3D2A09729F, 0x6878E501EC68E25C\n" ++
  "  .quad 0xCE032473295983E5, 0x1D1048C5D10A9A1B, 0x0D54005DB97678EC\n" ++
  "blm_k11_0_3:\n" ++
  "  .quad 0xC5B388641D9B6861, 0x5336E25CE3107193, 0xF1B33289F1B33083\n" ++
  "  .quad 0xD7F5E4656A8DBF25, 0x4E0609D307E55412, 0x1778E7166FCC6DB7\n" ++
  "blm_k11_0_4:\n" ++
  "  .quad 0x51154CE9AC8895D9, 0x985A286F301E77C4, 0x086EEB65982FAC18\n" ++
  "  .quad 0x99DB995A1257FB3F, 0x6642B4B3E4118E54, 0x0E99726A3199F443\n" ++
  "blm_k11_0_5:\n" ++
  "  .quad 0xCD13C1C66F652983, 0xA0870D2DCAE73D19, 0x9ED3AB9097E68F90\n" ++
  "  .quad 0xDB3CB17DD952799B, 0x01D1201BF7A74AB5, 0x1630C3250D7313FF\n" ++
  "blm_k11_0_6:\n" ++
  "  .quad 0xDDD7F225A139ED84, 0x8DA25128C1052ECA, 0x9008E218F9C86B2A\n" ++
  "  .quad 0xB11586264F0F8CE1, 0x6A3726C38AE652BF, 0x0D6ED6553FE44D29\n" ++
  "blm_k11_0_7:\n" ++
  "  .quad 0x9CCB5618E3F0C88E, 0x39B7C8F8C8F475AF, 0xA682C62EF0F27533\n" ++
  "  .quad 0x356DE5AB275B4DB1, 0xE8743884D1117E53, 0x17B81E7701ABDBE2\n" ++
  "blm_k11_0_8:\n" ++
  "  .quad 0x6D71986A8497E317, 0x4FA295F296B74E95, 0xA2C596C928C5D1DE\n" ++
  "  .quad 0xC43B756CE79F5574, 0x7B90B33563BE990D, 0x080D3CF1F9A78FC4\n" ++
  "blm_k11_0_9:\n" ++
  "  .quad 0x7F241067BE390C9E, 0xA3190B2EDC032779, 0x676314BAF4BB1B7F\n" ++
  "  .quad 0xDD2ECB803A0C5C99, 0x2E0C37515D138F22, 0x169B1F8E1BCFA7C4\n" ++
  "blm_k11_0_10:\n" ++
  "  .quad 0xCA67DF3F1605FB7B, 0xF69B771F8C285DEC, 0xD50AF36003B14866\n" ++
  "  .quad 0xFA7DCCDDE6787F96, 0x72D8EC09D2565B0D, 0x10321DA079CE07E2\n" ++
  "blm_k11_0_11:\n" ++
  "  .quad 0xA9C8BA2E8BA2D229, 0xC24B1B80B64D391F, 0x23C0BF1BC24C6B68\n" ++
  "  .quad 0x31D79D7E22C837BC, 0xBD1E962381EDEE3D, 0x06E08C248E260E70\n" ++
  "blm_k11_1_0:\n" ++
  "  .quad 0x993CF9FA40D21B1C, 0xB558D681BE343DF8, 0x9C9588617FC8AC62\n" ++
  "  .quad 0x01D5EF4BA35B48BA, 0x18B2E62F4BD3FA6F, 0x08CA8D548CFF19AE\n" ++
  "blm_k11_1_1:\n" ++
  "  .quad 0xE5C8276EC82B3BFF, 0x13DAA8846CB026E9, 0x0126C2588C48BF57\n" ++
  "  .quad 0x7041E8CA0CF0800C, 0x48B4711298E53636, 0x12561A5DEB559C43\n" ++
  "blm_k11_1_2:\n" ++
  "  .quad 0xFCC239BA5CB83E19, 0xD6A3D0967C94FEDC, 0xFCA64E00B11ACEAC\n" ++
  "  .quad 0x6F89416F5A718CD1, 0x8137E629BFF2991F, 0x0B2962FE57A3225E\n" ++
  "blm_k11_1_3:\n" ++
  "  .quad 0x130DE8938DC62CD8, 0x4976D5243EECF5C4, 0x54CCA8ABC28D6FD0\n" ++
  "  .quad 0x5B08243F16B16551, 0xC83AAFEF7C40EB54, 0x03425581A58AE2FE\n" ++
  "blm_k11_1_4:\n" ++
  "  .quad 0x539D395B3532A21E, 0x9BD29BA81F35781D, 0x8D6B44E833B306DA\n" ++
  "  .quad 0xFFDFC759A12062BB, 0x0A6F1D5F43E7A07D, 0x13A8E162022914A8\n" ++
  "blm_k11_1_5:\n" ++
  "  .quad 0xC02DF9A29F6304A5, 0x7400D24BC4228F11, 0x0A43BCEF24B8982F\n" ++
  "  .quad 0x395735E9CE9CAD4D, 0x55390F7F0506C6E9, 0x0E7355F8E4E667B9\n" ++
  "blm_k11_1_6:\n" ++
  "  .quad 0xEC2574496EE84A3A, 0xEA73B3538F0DE06C, 0x4E2E073062AEDE9C\n" ++
  "  .quad 0x570F5799AF53A189, 0x0F3E0C63E0596721, 0x0772CAACF1693619\n" ++
  "blm_k11_1_7:\n" ++
  "  .quad 0x11F7D99BBDCC5A5E, 0x0FA5B9489D11E2D3, 0x1996E1CDF9822C58\n" ++
  "  .quad 0x6E7F63C21BCA68A8, 0x30B3F5B074CF0199, 0x14A7AC2A9D64A8B2\n" ++
  "blm_k11_1_8:\n" ++
  "  .quad 0x4776EC3A79A1D641, 0x03826692ABBA4370, 0x74100DA67F398835\n" ++
  "  .quad 0xE07F8D1D7161366B, 0x5E920B3DAFC7A3CC, 0x0A10ECF6ADA54F82\n" ++
  "blm_k11_1_9:\n" ++
  "  .quad 0x2D6384D168ECDD0A, 0x93174E4B4B786500, 0x76DF533978F31C15\n" ++
  "  .quad 0xF682B4EE96F7D037, 0x476D6E3EB3A56680, 0x095FC13AB9E92AD4\n" ++
  "blm_k11_1_10:\n" ++
  "  .quad 0x0000000000000001, 0x0000000000000000, 0x0000000000000000\n" ++
  "  .quad 0x0000000000000000, 0x0000000000000000, 0x0000000000000000\n" ++
  "blm_k11_2_0:\n" ++
  "  .quad 0xBE9845719707BB33, 0xCD0C7AEE9B3BA3C2, 0x2B52AF6C956543D3\n" ++
  "  .quad 0x11AD138E48A86952, 0x259D1F094980DCFA, 0x090D97C81BA24EE0\n" ++
  "blm_k11_2_1:\n" ++
  "  .quad 0xE097E75A2E41C696, 0xD6C56711962FA8BF, 0x0F906343EB67AD34\n" ++
  "  .quad 0x1223E96C254F383D, 0xD51036D776FB4683, 0x134996A104EE5811\n" ++
  "blm_k11_2_2:\n" ++
  "  .quad 0xB8DFE240C72DE1F6, 0xD26D521628B00523, 0xC344BE4B91400DA7\n" ++
  "  .quad 0x2552E2D658A31CE2, 0xF4A384C86A3B4994, 0x00CC786BAA966E66\n" ++
  "blm_k11_2_3:\n" ++
  "  .quad 0xA6355C77B0E5F4CB, 0xDE405ABA9EC61DEC, 0x09E4A3EC03251CF9\n" ++
  "  .quad 0xD42AA7B90EEB791C, 0x7898751AD8746757, 0x01F86376E8981C21\n" ++
  "blm_k11_2_4:\n" ++
  "  .quad 0x41B6DAECF2E8FEDB, 0x2EE7F8DC099040A8, 0x79833FD221351ADC\n" ++
  "  .quad 0x195536FBE3CE50B8, 0x5CAF4FE2A21529C4, 0x08CC03FDEFE0FF13\n" ++
  "blm_k11_2_5:\n" ++
  "  .quad 0x99B23AB13633A5F0, 0x203F6326C95A8072, 0x76505C3D3AD5544E\n" ++
  "  .quad 0x74A7D0D4AFADB7BD, 0x2211E11DB8F0A6A0, 0x16603FCA40634B6A\n" ++
  "blm_k11_2_6:\n" ++
  "  .quad 0xC961F8855FE9D6F2, 0x47A87AC2460F415E, 0x5231413C4D634F37\n" ++
  "  .quad 0xE75BB8CA2BE184CB, 0xB2C977D027796B3C, 0x04AB0B9BCFAC1BBC\n" ++
  "blm_k11_2_7:\n" ++
  "  .quad 0xA15E4CA31870FB29, 0x42F64550FEDFE935, 0xFD038DA6C26C8426\n" ++
  "  .quad 0x170A05BFE3BDD81F, 0xDE9926BD2CA6C674, 0x0987C8D5333AB86F\n" ++
  "blm_k11_2_8:\n" ++
  "  .quad 0x60370E577BDBA587, 0x69D65201C78607A3, 0x1E8B6E6A1F20CABE\n" ++
  "  .quad 0x8F3ABD16679DC26C, 0xE88C9E221E4DA1BB, 0x09FC4018BD96684B\n" ++
  "blm_k11_2_9:\n" ++
  "  .quad 0x2BAFAAEBCA731C30, 0x9B3F7055DD4EBA6F, 0x06985E7ED1E4D43B\n" ++
  "  .quad 0xC42A0CA7915AF6FE, 0x223ABDE7ADA14A23, 0x0E1BBA7A1186BDB5\n" ++
  "blm_k11_2_10:\n" ++
  "  .quad 0xE813711AD011C132, 0x31BF3A5CCE3FBAFC, 0xD1183E416389E610\n" ++
  "  .quad 0xCD2FCBCB6CAF493F, 0x0DFD0B8F1D43FB93, 0x19713E47937CD1BE\n" ++
  "blm_k11_2_11:\n" ++
  "  .quad 0xCE07C8A4D0074D8E, 0x49D9CDF41B44D606, 0x2E6BFE7F911F6432\n" ++
  "  .quad 0x523559B8AAF0C246, 0xB918C143FED2EDCC, 0x18B46A908F36F6DE\n" ++
  "blm_k11_2_12:\n" ++
  "  .quad 0x0D4C04F00B971EF8, 0x06C851C1919211F2, 0xC02710E807B4633F\n" ++
  "  .quad 0x7AA7B12A3426B08E, 0xD155096004F53F44, 0x0B182CAC101B9399\n" ++
  "blm_k11_2_13:\n" ++
  "  .quad 0x42D9D3F5DB980133, 0xC6CF90AD1C232A64, 0x13E6632D3C40659C\n" ++
  "  .quad 0x757B3B080D4C1580, 0x72FC00AE7BE315DC, 0x0245A394AD1ECA9B\n" ++
  "blm_k11_2_14:\n" ++
  "  .quad 0x866B1E715475224B, 0x6BA1049B6579AFB7, 0xD9AB0F5D396A7CE4\n" ++
  "  .quad 0x5E673D81D7E86568, 0x02A159F748C4A3FC, 0x05C129645E44CF11\n" ++
  "blm_k11_2_15:\n" ++
  "  .quad 0x04B456BE69C8B604, 0xB665027EFEC01C77, 0x57ADD4FA95AF01B2\n" ++
  "  .quad 0xCB181D8F84965A39, 0x4EA50B3B42DF2EB5, 0x15E6BE4E990F03CE\n" ++
  "blm_k11_3_0:\n" ++
  "  .quad 0x01479253B03663C1, 0x07F3688EF60C206D, 0xEEC3232B5BE72E7A\n" ++
  "  .quad 0x601A6DE578980BE6, 0x52181140FAD0EAE9, 0x16112C4C3A9C98B2\n" ++
  "blm_k11_3_1:\n" ++
  "  .quad 0x32F6102C2E49A03D, 0x78A4260763529E35, 0xA4A10356F453E01F\n" ++
  "  .quad 0x85C84FF731C4D59C, 0x1A0CBD6C43C348B8, 0x1962D75C2381201E\n" ++
  "blm_k11_3_2:\n" ++
  "  .quad 0x1E2538B53DBF67F2, 0xA6757CD636F96F89, 0x0C35A5DD279CD2EC\n" ++
  "  .quad 0x78C4855551AE7F31, 0x6FAAAE7D6E8EB157, 0x058DF3306640DA27\n" ++
  "blm_k11_3_3:\n" ++
  "  .quad 0xA8D26D98445F5416, 0x727364F2C28297AD, 0x123DA489E726AF41\n" ++
  "  .quad 0xD115C5DBDDBCD30E, 0xF20D23BF89EDB4D1, 0x16B7D288798E5395\n" ++
  "blm_k11_3_4:\n" ++
  "  .quad 0xDA39142311A5001D, 0xA20B15DC0FD2EDED, 0x542EDA0FC9DEC916\n" ++
  "  .quad 0xC6D19C9F0F69BBB0, 0xB00CC912F8228DDC, 0x0BE0E079545F43E4\n" ++
  "blm_k11_3_5:\n" ++
  "  .quad 0x02C6477FAAF9B7AC, 0x49F38DB9DFA9CCE2, 0xC5ECD87B6F0F5A64\n" ++
  "  .quad 0xB70152C65550D881, 0x9FB266EAAC783182, 0x08D9E5297186DB2D\n" ++
  "blm_k11_3_6:\n" ++
  "  .quad 0x3D1A1399126A775C, 0xD5FA9C01A58B1FB9, 0x5DD365BC400A0051\n" ++
  "  .quad 0x5EECFDFA8D0CF8EF, 0xC3BA8734ACE9824B, 0x166007C08A99DB2F\n" ++
  "blm_k11_3_7:\n" ++
  "  .quad 0x60EE415A15812ED9, 0xB920F5B00801DEE4, 0xFEB34FD206357132\n" ++
  "  .quad 0xE5A4375EFA1F4FD7, 0x03BCDDFABBA6FF6E, 0x16A3EF08BE3EA7EA\n" ++
  "blm_k11_3_8:\n" ++
  "  .quad 0x6B233D9D55535D4A, 0x52CFE2F7BB924883, 0xABC5750C4BF39B48\n" ++
  "  .quad 0xF9FB0CE4C6AF5920, 0x1A1BE54FD1D74CC4, 0x1866C8ED336C6123\n" ++
  "blm_k11_3_9:\n" ++
  "  .quad 0x346EF48BB8913F55, 0xC7385EA3D529B35E, 0x5308592E7EA7D4FB\n" ++
  "  .quad 0x3216F763E13D87BB, 0xEA820597D94A8490, 0x167A55CDA70A6E1C\n" ++
  "blm_k11_3_10:\n" ++
  "  .quad 0x00F8B49CBA8F6AA8, 0x71A5C29F4F830604, 0x0E591B36E636A5C8\n" ++
  "  .quad 0x9C6DD039BB61A629, 0x48F010A01AD2911D, 0x04D2F259EEA405BD\n" ++
  "blm_k11_3_11:\n" ++
  "  .quad 0x9684B529E2561092, 0x16F968986F7EBBEA, 0x8C0F9A88CEA79135\n" ++
  "  .quad 0x7F94FF8AEFCE42D2, 0xF5852C1E48C50C47, 0x0ACCBB67481D033F\n" ++
  "blm_k11_3_12:\n" ++
  "  .quad 0x1E99B138573345CC, 0x93000763E3B90AC1, 0x7D5CEEF9A00D9B86\n" ++
  "  .quad 0x543346D98ADF0226, 0xC3613144B45F1496, 0x0AD6B9514C767FE3\n" ++
  "blm_k11_3_13:\n" ++
  "  .quad 0xD1FADC1326ED06F7, 0x420517BD8714CC80, 0xCB748DF27942480E\n" ++
  "  .quad 0xBF565B94E72927C1, 0x628BDD0D53CD76F2, 0x02660400EB2E4F3B\n" ++
  "blm_k11_3_14:\n" ++
  "  .quad 0x4415473A1D634B8F, 0x5CA2F570F1349780, 0x324EFCD6356CAA20\n" ++
  "  .quad 0x71C40F65E273B853, 0x6B24255E0D7819C1, 0x0E0FA1D816DDC03E\n" ++
  "blm_k11_3_15:\n" ++
  "  .quad 0x0000000000000001, 0x0000000000000000, 0x0000000000000000\n" ++
  "  .quad 0x0000000000000000, 0x0000000000000000, 0x0000000000000000\n" ++
  "blm_iso3_a:\n" ++
  "  .quad 0x0000000000000000, 0x0000000000000000, 0x0000000000000000\n" ++
  "  .quad 0x0000000000000000, 0x0000000000000000, 0x0000000000000000\n" ++
  "  .quad 0x00000000000000F0, 0x0000000000000000, 0x0000000000000000\n" ++
  "  .quad 0x0000000000000000, 0x0000000000000000, 0x0000000000000000\n" ++
  "blm_iso3_b:\n" ++
  "  .quad 0x00000000000003F4, 0x0000000000000000, 0x0000000000000000\n" ++
  "  .quad 0x0000000000000000, 0x0000000000000000, 0x0000000000000000\n" ++
  "  .quad 0x00000000000003F4, 0x0000000000000000, 0x0000000000000000\n" ++
  "  .quad 0x0000000000000000, 0x0000000000000000, 0x0000000000000000\n" ++
  "blm_iso3_z:\n" ++
  "  .quad 0xB9FEFFFFFFFFAAA9, 0x1EABFFFEB153FFFF, 0x6730D2A0F6B0F624\n" ++
  "  .quad 0x64774B84F38512BF, 0x4B1BA7B6434BACD7, 0x1A0111EA397FE69A\n" ++
  "  .quad 0xB9FEFFFFFFFFAAAA, 0x1EABFFFEB153FFFF, 0x6730D2A0F6B0F624\n" ++
  "  .quad 0x64774B84F38512BF, 0x4B1BA7B6434BACD7, 0x1A0111EA397FE69A\n" ++
  "blm_eta_0:\n" ++
  "  .quad 0x27B5AFBDF1BF1C90, 0x498255A2AAEC0AC6, 0x3B7F4A947E02D978\n" ++
  "  .quad 0xB0E85A117402DFD8, 0x5E5BF892AD5D2CC7, 0x0699BE3B8C687096\n" ++
  "  .quad 0x7BABA37F2183E9B5, 0x36D965026ADAD3EF, 0xCA07E27089A2CE24\n" ++
  "  .quad 0x288020B5B8A9CC99, 0x5DD0972B6E3949E4, 0x08157CD83046453F\n" ++
  "blm_eta_1:\n" ++
  "  .quad 0x3E535C80DE7BC0F6, 0xE7D29AFC46792C10, 0x9D28F0306D0E27FF\n" ++
  "  .quad 0x3BF72ACF3ADB4625, 0xED4B108AD51262F3, 0x11EB95120939A15A\n" ++
  "  .quad 0x27B5AFBDF1BF1C90, 0x498255A2AAEC0AC6, 0x3B7F4A947E02D978\n" ++
  "  .quad 0xB0E85A117402DFD8, 0x5E5BF892AD5D2CC7, 0x0699BE3B8C687096\n" ++
  "blm_eta_2:\n" ++
  "  .quad 0x0EDBC653A72DEE17, 0x47CF08CE6C6317F4, 0xAD5EC46A0B7A3B02\n" ++
  "  .quad 0x44FD562F6F72BC5B, 0xA155231EB3E71BA0, 0x0AB1C2FFDD6C253C\n" ++
  "  .quad 0x87BF597FBF7F8FC1, 0x06DF72162A3D3E02, 0x73CC37E0181271E0\n" ++
  "  .quad 0xAC1967C7544B4478, 0x64480885D68AD0CC, 0x0AA4048667067228\n" ++
  "blm_eta_3:\n" ++
  "  .quad 0x323FA68040801AEA, 0x17CC8DE88716C1FD, 0xF3649AC0DE9E8444\n" ++
  "  .quad 0xB85DE3BD9F39CE46, 0xE6D39F306CC0DC0A, 0x0F5D0D63D2797471\n" ++
  "  .quad 0x0EDBC653A72DEE17, 0x47CF08CE6C6317F4, 0xAD5EC46A0B7A3B02\n" ++
  "  .quad 0x44FD562F6F72BC5B, 0xA155231EB3E71BA0, 0x0AB1C2FFDD6C253C\n" ++
  "blm_root8_0:\n" ++
  "  .quad 0x0000000000000001, 0x0000000000000000, 0x0000000000000000\n" ++
  "  .quad 0x0000000000000000, 0x0000000000000000, 0x0000000000000000\n" ++
  "  .quad 0x0000000000000000, 0x0000000000000000, 0x0000000000000000\n" ++
  "  .quad 0x0000000000000000, 0x0000000000000000, 0x0000000000000000\n" ++
  "blm_root8_1:\n" ++
  "  .quad 0x0000000000000000, 0x0000000000000000, 0x0000000000000000\n" ++
  "  .quad 0x0000000000000000, 0x0000000000000000, 0x0000000000000000\n" ++
  "  .quad 0x0000000000000001, 0x0000000000000000, 0x0000000000000000\n" ++
  "  .quad 0x0000000000000000, 0x0000000000000000, 0x0000000000000000\n" ++
  "blm_root8_2:\n" ++
  "  .quad 0xC81084FBEDE3CC09, 0xEE67992F72EC05F4, 0x77F76E17009241C5\n" ++
  "  .quad 0x48395DABC2D3435E, 0x6831E36D6BD17FFE, 0x06AF0E0437FF400B\n" ++
  "  .quad 0xC81084FBEDE3CC09, 0xEE67992F72EC05F4, 0x77F76E17009241C5\n" ++
  "  .quad 0x48395DABC2D3435E, 0x6831E36D6BD17FFE, 0x06AF0E0437FF400B\n" ++
  "blm_root8_3:\n" ++
  "  .quad 0xC81084FBEDE3CC09, 0xEE67992F72EC05F4, 0x77F76E17009241C5\n" ++
  "  .quad 0x48395DABC2D3435E, 0x6831E36D6BD17FFE, 0x06AF0E0437FF400B\n" ++
  "  .quad 0xF1EE7B04121BDEA2, 0x304466CF3E67FA0A, 0xEF396489F61EB45E\n" ++
  "  .quad 0x1C3DEDD930B1CF60, 0xE2E9C448D77A2CD9, 0x135203E60180A68E\n" ++
  "blm_pm9d16:\n" ++
  "  .quad 0xB26AA00001C718E3, 0xD7CED6B1D76382EA, 0x3162C338362113CF\n" ++
  "  .quad 0x966BF91ED3E71B74, 0xB292E85A87091A04, 0x11D68619C86185C7\n" ++
  "  .quad 0xEF53149330978EF0, 0x050A62CFD16DDCA6, 0x466E59E49349E8BD\n" ++
  "  .quad 0x9E2DC90E50E7046B, 0x74BD278EAA22F25E, 0x002A437A4B8C35FC\n" ++
  "blm_k3_0_0:\n" ++
  "  .quad 0x6238AAAAAAAA97D6, 0x5C2638E343D9C71C, 0x88B58423C50AE15D\n" ++
  "  .quad 0x32C52D39FD3A042A, 0xBB5B7A9A47D7ED85, 0x05C759507E8E333E\n" ++
  "  .quad 0x6238AAAAAAAA97D6, 0x5C2638E343D9C71C, 0x88B58423C50AE15D\n" ++
  "  .quad 0x32C52D39FD3A042A, 0xBB5B7A9A47D7ED85, 0x05C759507E8E333E\n" ++
  "blm_k3_0_1:\n" ++
  "  .quad 0x0000000000000000, 0x0000000000000000, 0x0000000000000000\n" ++
  "  .quad 0x0000000000000000, 0x0000000000000000, 0x0000000000000000\n" ++
  "  .quad 0x26A9FFFFFFFFC71A, 0x1472AAA9CB8D5555, 0x9A208C6B4F20A418\n" ++
  "  .quad 0x984F87ADF7AE0C7F, 0x32126FCED787C88F, 0x11560BF17BAA99BC\n" ++
  "blm_k3_0_2:\n" ++
  "  .quad 0x26A9FFFFFFFFC71E, 0x1472AAA9CB8D5555, 0x9A208C6B4F20A418\n" ++
  "  .quad 0x984F87ADF7AE0C7F, 0x32126FCED787C88F, 0x11560BF17BAA99BC\n" ++
  "  .quad 0x9354FFFFFFFFE38D, 0x0A395554E5C6AAAA, 0xCD104635A790520C\n" ++
  "  .quad 0xCC27C3D6FBD7063F, 0x190937E76BC3E447, 0x08AB05F8BDD54CDE\n" ++
  "blm_k3_0_3:\n" ++
  "  .quad 0x88E2AAAAAAAA5ED1, 0x7098E38D0F671C71, 0x22D6108F142B8575\n" ++
  "  .quad 0xCB14B4E7F4E810AA, 0xED6DEA691F5FB614, 0x171D6541FA38CCFA\n" ++
  "  .quad 0x0000000000000000, 0x0000000000000000, 0x0000000000000000\n" ++
  "  .quad 0x0000000000000000, 0x0000000000000000, 0x0000000000000000\n" ++
  "blm_k3_1_0:\n" ++
  "  .quad 0x0000000000000000, 0x0000000000000000, 0x0000000000000000\n" ++
  "  .quad 0x0000000000000000, 0x0000000000000000, 0x0000000000000000\n" ++
  "  .quad 0xB9FEFFFFFFFFAA63, 0x1EABFFFEB153FFFF, 0x6730D2A0F6B0F624\n" ++
  "  .quad 0x64774B84F38512BF, 0x4B1BA7B6434BACD7, 0x1A0111EA397FE69A\n" ++
  "blm_k3_1_1:\n" ++
  "  .quad 0x000000000000000C, 0x0000000000000000, 0x0000000000000000\n" ++
  "  .quad 0x0000000000000000, 0x0000000000000000, 0x0000000000000000\n" ++
  "  .quad 0xB9FEFFFFFFFFAA9F, 0x1EABFFFEB153FFFF, 0x6730D2A0F6B0F624\n" ++
  "  .quad 0x64774B84F38512BF, 0x4B1BA7B6434BACD7, 0x1A0111EA397FE69A\n" ++
  "blm_k3_1_2:\n" ++
  "  .quad 0x0000000000000001, 0x0000000000000000, 0x0000000000000000\n" ++
  "  .quad 0x0000000000000000, 0x0000000000000000, 0x0000000000000000\n" ++
  "  .quad 0x0000000000000000, 0x0000000000000000, 0x0000000000000000\n" ++
  "  .quad 0x0000000000000000, 0x0000000000000000, 0x0000000000000000\n" ++
  "blm_k3_1_3:\n" ++
  "  .quad 0x0000000000000000, 0x0000000000000000, 0x0000000000000000\n" ++
  "  .quad 0x0000000000000000, 0x0000000000000000, 0x0000000000000000\n" ++
  "  .quad 0x0000000000000000, 0x0000000000000000, 0x0000000000000000\n" ++
  "  .quad 0x0000000000000000, 0x0000000000000000, 0x0000000000000000\n" ++
  "blm_k3_2_0:\n" ++
  "  .quad 0x12CFC71C71C6D706, 0xFC8C25EBF8C92F68, 0xF54439D87D27E500\n" ++
  "  .quad 0x0F7DA5D4A07F649B, 0x59A4C18B076D1193, 0x1530477C7AB4113B\n" ++
  "  .quad 0x12CFC71C71C6D706, 0xFC8C25EBF8C92F68, 0xF54439D87D27E500\n" ++
  "  .quad 0x0F7DA5D4A07F649B, 0x59A4C18B076D1193, 0x1530477C7AB4113B\n" ++
  "blm_k3_2_1:\n" ++
  "  .quad 0x0000000000000000, 0x0000000000000000, 0x0000000000000000\n" ++
  "  .quad 0x0000000000000000, 0x0000000000000000, 0x0000000000000000\n" ++
  "  .quad 0x6238AAAAAAAA97BE, 0x5C2638E343D9C71C, 0x88B58423C50AE15D\n" ++
  "  .quad 0x32C52D39FD3A042A, 0xBB5B7A9A47D7ED85, 0x05C759507E8E333E\n" ++
  "blm_k3_2_2:\n" ++
  "  .quad 0x26A9FFFFFFFFC71C, 0x1472AAA9CB8D5555, 0x9A208C6B4F20A418\n" ++
  "  .quad 0x984F87ADF7AE0C7F, 0x32126FCED787C88F, 0x11560BF17BAA99BC\n" ++
  "  .quad 0x9354FFFFFFFFE38F, 0x0A395554E5C6AAAA, 0xCD104635A790520C\n" ++
  "  .quad 0xCC27C3D6FBD7063F, 0x190937E76BC3E447, 0x08AB05F8BDD54CDE\n" ++
  "blm_k3_2_3:\n" ++
  "  .quad 0xE1B371C71C718B10, 0x4E79097A56DC4BD9, 0xB0E977C69AA27452\n" ++
  "  .quad 0x761B0F37A1E26286, 0xFBF7043DE3811AD0, 0x124C9AD43B6CF79B\n" ++
  "  .quad 0x0000000000000000, 0x0000000000000000, 0x0000000000000000\n" ++
  "  .quad 0x0000000000000000, 0x0000000000000000, 0x0000000000000000\n" ++
  "blm_k3_3_0:\n" ++
  "  .quad 0xB9FEFFFFFFFFA8FB, 0x1EABFFFEB153FFFF, 0x6730D2A0F6B0F624\n" ++
  "  .quad 0x64774B84F38512BF, 0x4B1BA7B6434BACD7, 0x1A0111EA397FE69A\n" ++
  "  .quad 0xB9FEFFFFFFFFA8FB, 0x1EABFFFEB153FFFF, 0x6730D2A0F6B0F624\n" ++
  "  .quad 0x64774B84F38512BF, 0x4B1BA7B6434BACD7, 0x1A0111EA397FE69A\n" ++
  "blm_k3_3_1:\n" ++
  "  .quad 0x0000000000000000, 0x0000000000000000, 0x0000000000000000\n" ++
  "  .quad 0x0000000000000000, 0x0000000000000000, 0x0000000000000000\n" ++
  "  .quad 0xB9FEFFFFFFFFA9D3, 0x1EABFFFEB153FFFF, 0x6730D2A0F6B0F624\n" ++
  "  .quad 0x64774B84F38512BF, 0x4B1BA7B6434BACD7, 0x1A0111EA397FE69A\n" ++
  "blm_k3_3_2:\n" ++
  "  .quad 0x0000000000000012, 0x0000000000000000, 0x0000000000000000\n" ++
  "  .quad 0x0000000000000000, 0x0000000000000000, 0x0000000000000000\n" ++
  "  .quad 0xB9FEFFFFFFFFAA99, 0x1EABFFFEB153FFFF, 0x6730D2A0F6B0F624\n" ++
  "  .quad 0x64774B84F38512BF, 0x4B1BA7B6434BACD7, 0x1A0111EA397FE69A\n" ++
  "blm_k3_3_3:\n" ++
  "  .quad 0x0000000000000001, 0x0000000000000000, 0x0000000000000000\n" ++
  "  .quad 0x0000000000000000, 0x0000000000000000, 0x0000000000000000\n" ++
  "  .quad 0x0000000000000000, 0x0000000000000000, 0x0000000000000000\n" ++
  "  .quad 0x0000000000000000, 0x0000000000000000, 0x0000000000000000\n" ++
  "blm_heff_g2:\n" ++
  "  .quad 0xE8020005AAA95551, 0x59894C0ADEBBF6B4, 0xE954CBC06689F6A3\n" ++
  "  .quad 0x2EC0EC69D7477C1A, 0x6D82BF015D1212B0, 0x329C2F178731DB95\n" ++
  "  .quad 0x9986FF031508FFE1, 0x88E2A8E9145AD768, 0x584C6A0EA91B3528\n" ++
  "  .quad 0x0BC69F08F2EE75B3\n" ++
  ".balign 8\n"

/-- Fp dst = base ^ exp (MSB-first square-and-multiply; Arith384Mod is
    read-then-write so squaring/multiplying in place is safe).
    a0 = dst, a1 = base, a2 = exp (LE limbs), a3 = top bit. dst must
    not alias base. -/
def blmFpPow_prog : Program :=
  [ .ADDI .x2 .x2 (-48 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x21 (8 : BitVec 12),
    .SD .x2 .x22 (16 : BitVec 12),
    .SD .x2 .x23 (24 : BitVec 12),
    .SD .x2 .x24 (32 : BitVec 12),
    .MV .x21 .x10,
    .MV .x22 .x11,
    .MV .x23 .x12,
    .MV .x24 .x13,
    .AUIPC .x10 (laHi GuestAddrs.blsf_le_one (GuestAddrs.blm_fp_pow + 40)),
    .ADDI .x10 .x10 (laLo GuestAddrs.blsf_le_one (GuestAddrs.blm_fp_pow + 40)),
    .MV .x11 .x21,
    .LI .x12 (6 : Word),
    .JAL .x1 (jalOff GuestAddrs.blsf_copy_quads (GuestAddrs.blm_fp_pow + 56)),
    .MV .x10 .x21,
    .MV .x11 .x21,
    .MV .x12 .x21,
    .JAL .x1 (jalOff GuestAddrs.blsg2_fp_mul (GuestAddrs.blm_fp_pow + 72)),
    .SRLI .x5 .x24 (6 : BitVec 6),
    .SLLI .x5 .x5 (3 : BitVec 6),
    .ADD .x5 .x23 .x5,
    .LD .x6 .x5 (0 : BitVec 12),
    .ANDI .x7 .x24 (63 : BitVec 12),
    .SRL .x6 .x6 .x7,
    .ANDI .x6 .x6 (1 : BitVec 12),
    .BEQ .x6 .x0 (20 : BitVec 13),
    .MV .x10 .x21,
    .MV .x11 .x22,
    .MV .x12 .x21,
    .JAL .x1 (jalOff GuestAddrs.blsg2_fp_mul (GuestAddrs.blm_fp_pow + 120)),
    .BEQ .x24 .x0 (12 : BitVec 13),
    .ADDI .x24 .x24 (-1 : BitVec 12),
    .JAL .x0 (-72 : BitVec 21),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x21 .x2 (8 : BitVec 12),
    .LD .x22 .x2 (16 : BitVec 12),
    .LD .x23 .x2 (24 : BitVec 12),
    .LD .x24 .x2 (32 : BitVec 12),
    .ADDI .x2 .x2 (48 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `blmFpPow_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def blmFpPow_relocs : RelocTable :=
  [ (10, .la .x10 "blsf_le_one"),
    (14, .jal .x1 "blsf_copy_quads"),
    (18, .jal .x1 "blsg2_fp_mul"),
    (30, .jal .x1 "blsg2_fp_mul") ]

def bls12MapFpPowFunction : String :=
  "blm_fp_pow:\n" ++ emitProgramR blmFpPow_prog blmFpPow_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `blmFpPow_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem bls12MapFpPowFunction_eq_prog :
    bls12MapFpPowFunction = "blm_fp_pow:\n" ++ emitProgramR blmFpPow_prog blmFpPow_relocs := rfl

#guard bls12MapFpPowFunction.startsWith "blm_fp_pow:\n"
/-- Fp2 dst = base ^ exp (mutating complex-accelerator ops; in-place
    squaring is safe). a0 = dst, a1 = base, a2 = exp, a3 = top bit.
    dst must not alias base. -/
def blmFp2Pow_prog : Program :=
  [ .ADDI .x2 .x2 (-48 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x21 (8 : BitVec 12),
    .SD .x2 .x22 (16 : BitVec 12),
    .SD .x2 .x23 (24 : BitVec 12),
    .SD .x2 .x24 (32 : BitVec 12),
    .MV .x21 .x10,
    .MV .x22 .x11,
    .MV .x23 .x12,
    .MV .x24 .x13,
    .MV .x10 .x21,
    .LI .x5 (12 : Word),
    .SD .x10 .x0 (0 : BitVec 12),
    .ADDI .x10 .x10 (8 : BitVec 12),
    .ADDI .x5 .x5 (-1 : BitVec 12),
    .BNE .x5 .x0 (-12 : BitVec 13),
    .LI .x5 (1 : Word),
    .SD .x21 .x5 (0 : BitVec 12),
    .MV .x10 .x21,
    .MV .x11 .x21,
    .JAL .x1 (jalOff GuestAddrs.blsg2_fp2_mul (GuestAddrs.blm_fp2_pow + 80)),
    .SRLI .x5 .x24 (6 : BitVec 6),
    .SLLI .x5 .x5 (3 : BitVec 6),
    .ADD .x5 .x23 .x5,
    .LD .x6 .x5 (0 : BitVec 12),
    .ANDI .x7 .x24 (63 : BitVec 12),
    .SRL .x6 .x6 .x7,
    .ANDI .x6 .x6 (1 : BitVec 12),
    .BEQ .x6 .x0 (16 : BitVec 13),
    .MV .x10 .x21,
    .MV .x11 .x22,
    .JAL .x1 (jalOff GuestAddrs.blsg2_fp2_mul (GuestAddrs.blm_fp2_pow + 124)),
    .BEQ .x24 .x0 (12 : BitVec 13),
    .ADDI .x24 .x24 (-1 : BitVec 12),
    .JAL .x0 (-64 : BitVec 21),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x21 .x2 (8 : BitVec 12),
    .LD .x22 .x2 (16 : BitVec 12),
    .LD .x23 .x2 (24 : BitVec 12),
    .LD .x24 .x2 (32 : BitVec 12),
    .ADDI .x2 .x2 (48 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `blmFp2Pow_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def blmFp2Pow_relocs : RelocTable :=
  [ (20, .jal .x1 "blsg2_fp2_mul"),
    (31, .jal .x1 "blsg2_fp2_mul") ]

def bls12MapFp2PowFunction : String :=
  "blm_fp2_pow:\n" ++ emitProgramR blmFp2Pow_prog blmFp2Pow_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `blmFp2Pow_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem bls12MapFp2PowFunction_eq_prog :
    bls12MapFp2PowFunction = "blm_fp2_pow:\n" ++ emitProgramR blmFp2Pow_prog blmFp2Pow_relocs := rfl

#guard bls12MapFp2PowFunction.startsWith "blm_fp2_pow:\n"
/-- The map-precompile suite, ON TOP of the blsg_/blsg2_ suites. -/
def bls12MapKernelFunctions : String :=
  bls12MapFpPowFunction ++ "\n" ++
  bls12MapFp2PowFunction ++ "\n" ++
  zkvmBls12MapFpToG1RealFunction ++ "\n" ++
  zkvmBls12MapFp2ToG2RealFunction

/-- Probe (map_fp_to_g1): raw 64-byte wire felt at `0x40000008`;
    status u64 at OUTPUT+0 and the 96-byte compact result at +8. -/
def ziskBls12MapFpToG1RealProbePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a0, 0x40000008\n" ++
  "  li a1, 0xa0010008\n" ++
  "  jal ra, zkvm_bls12_map_fp_to_g1\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lblm1_probe_done\n" ++
  bls12G1PrecompileFunctions ++ "\n" ++
  bls12G2PrecompileFunctions ++ "\n" ++
  bls12MapKernelFunctions ++ "\n" ++
  ".Lblm1_probe_done:"


/-- Probe (map_fp2_to_g2): raw 128-byte wire Fp2 at `0x40000008`;
    status u64 at OUTPUT+0 and the 192-byte compact result at +8. -/
def ziskBls12MapFp2ToG2RealProbePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a0, 0x40000008\n" ++
  "  li a1, 0xa0010008\n" ++
  "  jal ra, zkvm_bls12_map_fp2_to_g2\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lblm2_probe_done\n" ++
  bls12G1PrecompileFunctions ++ "\n" ++
  bls12G2PrecompileFunctions ++ "\n" ++
  bls12MapKernelFunctions ++ "\n" ++
  ".Lblm2_probe_done:"


end EvmAsm.Codegen
