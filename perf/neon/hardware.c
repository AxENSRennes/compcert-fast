/* Differential-test adapter. Actual Advanced SIMD operations execute here.
   Distributed under the repository's INRIA Non-Commercial License Agreement. */
#include <arm_neon.h>
#include <stdint.h>
#include <string.h>
#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/alloc.h>
#include <caml/fail.h>

#if !defined(__aarch64__) || !defined(__ARM_NEON)
#error This test requires native AArch64 Advanced SIMD
#endif

static uint8x16_t vector_op(int width, int op, uint8x16_t a, uint8x16_t b)
{
    if (op == 3) return vandq_u8(a, b);
    if (op == 4) return vorrq_u8(a, b);
    if (op == 5) return veorq_u8(a, b);
    switch (width) {
    case 8:
        if (op == 0) return vaddq_u8(a, b);
        if (op == 1) return vsubq_u8(a, b);
        return vmulq_u8(a, b);
    case 16: {
        uint16x8_t x = vreinterpretq_u16_u8(a), y = vreinterpretq_u16_u8(b);
        if (op == 0) return vreinterpretq_u8_u16(vaddq_u16(x, y));
        if (op == 1) return vreinterpretq_u8_u16(vsubq_u16(x, y));
        return vreinterpretq_u8_u16(vmulq_u16(x, y));
    }
    case 32: {
        uint32x4_t x = vreinterpretq_u32_u8(a), y = vreinterpretq_u32_u8(b);
        if (op == 0) return vreinterpretq_u8_u32(vaddq_u32(x, y));
        if (op == 1) return vreinterpretq_u8_u32(vsubq_u32(x, y));
        return vreinterpretq_u8_u32(vmulq_u32(x, y));
    }
    default: {
        uint64x2_t x = vreinterpretq_u64_u8(a), y = vreinterpretq_u64_u8(b);
        if (op == 0) return vreinterpretq_u8_u64(vaddq_u64(x, y));
        return vreinterpretq_u8_u64(vsubq_u64(x, y));
    }
    }
}

CAMLprim value compcert_neon_eval(value vwidth, value vop, value va, value vb)
{
    CAMLparam4(vwidth, vop, va, vb);
    CAMLlocal1(output);
    int width = Int_val(vwidth), op = Int_val(vop);
    mlsize_t size = caml_string_length(va);
    if ((width != 8 && width != 16 && width != 32 && width != 64)
        || op < 0 || op > 5 || (op == 2 && width == 64))
        caml_invalid_argument("unsupported NEON instruction");
    size_t lane_bytes = (size_t)width / 8;
    if (size != caml_string_length(vb) || size % lane_bytes)
        caml_invalid_argument("invalid NEON input lengths");
    output = caml_alloc_string(size);
    const uint8_t *a = (const uint8_t *)String_val(va);
    const uint8_t *b = (const uint8_t *)String_val(vb);
    uint8_t *dst = (uint8_t *)Bytes_val(output);
    size_t offset = 0;
    for (; offset + 16 <= size; offset += 16)
        vst1q_u8(dst + offset, vector_op(width, op, vld1q_u8(a + offset), vld1q_u8(b + offset)));
    for (; offset < size; offset += lane_bytes) {
        uint64_t x = 0, y = 0, z;
        memcpy(&x, a + offset, lane_bytes);
        memcpy(&y, b + offset, lane_bytes);
        switch (op) {
        case 0: z = x + y; break;
        case 1: z = x - y; break;
        case 2: z = x * y; break;
        case 3: z = x & y; break;
        case 4: z = x | y; break;
        default: z = x ^ y; break;
        }
        memcpy(dst + offset, &z, lane_bytes);
    }
    CAMLreturn(output);
}

/* An unsupported vector operation must select the ordinary scalar path. */
CAMLprim value compcert_scalar_u64_mul(value va, value vb)
{
    CAMLparam2(va, vb);
    CAMLlocal1(output);
    mlsize_t size = caml_string_length(va);
    if (size != caml_string_length(vb) || size % 8)
        caml_invalid_argument("invalid scalar uint64 lengths");
    output = caml_alloc_string(size);
    const uint8_t *a = (const uint8_t *)String_val(va);
    const uint8_t *b = (const uint8_t *)String_val(vb);
    uint8_t *dst = (uint8_t *)Bytes_val(output);
    for (size_t offset = 0; offset < size; offset += 8) {
        uint64_t x, y, z;
        memcpy(&x, a + offset, 8);
        memcpy(&y, b + offset, 8);
        z = x * y;
        memcpy(dst + offset, &z, 8);
    }
    CAMLreturn(output);
}
