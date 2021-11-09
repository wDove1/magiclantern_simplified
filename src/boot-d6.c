/** \file
 * Startup code for DIGIC 6
 */

#include "dryos.h"
#include "boot.h"

/** These are called when new tasks are created */
static int my_init_task(int a, int b, int c, int d);

/** This just goes into the bss */
#define RELOCSIZE 0x3D100  // look in HIJACK macros for the highest address, and subtract ROMBASEADDR; 0x50000 was too much for 750D
#define MOV_ALIGNMENT 0x8000 // mov.w encoding doesn't give us many bits for address.
                             // 0x8000 makes the sums easier, while still allowing a reasonable range of addresses.
                             // You get a kind of large 32kB granularity though.

static uint32_t _reloc[ RELOCSIZE / 4 ];
#define RELOCADDR ((uintptr_t) _reloc)

/** Encoding for the Thumb instructions used for patching the boot code */
#define THUMB_RET_INSTR 0x00004770        /* BX LR */

static inline uint32_t thumb_branch_instr(uint32_t pc, uint32_t dest, uint32_t opcode)
{
    /* thanks atonal */
    uint32_t offset = dest - ((pc + 4) & ~3); /* according to datasheets, this should be the correct calculation -> ALIGN(PC, 4) */
    uint32_t s = (offset >> 24) & 1;
    uint32_t i1 = (offset >> 23) & 1;
    uint32_t i2 = (offset >> 22) & 1;
    uint32_t imm10 = (offset >> 12) & 0x3ff;
    uint32_t imm11 = (offset >> 1) & 0x7ff;
    uint32_t j1 = (!(i1 ^ s)) & 0x1;
    uint32_t j2 = (!(i2 ^ s)) & 0x1;

    return opcode | (s << 10) | imm10 | (j1 << 29) | (j2 << 27) | (imm11 << 16);
}

#define THUMB_B_W_INSTR(pc,dest)    thumb_branch_instr((uint32_t)(pc), (uint32_t)(dest), 0x9000f000)
#define THUMB_BLX_INSTR(pc,dest)    thumb_branch_instr((uint32_t)(pc), (uint32_t)(dest), 0xc000f000)

#define INSTR( addr ) ( *(uint32_t*)( (addr) - ROMBASEADDR + RELOCADDR ) )

/** Fix a branch instruction in the relocated firmware image */
#define FIXUP_BRANCH( rom_addr, dest_addr ) \
    qprint("[BOOT] fixing up branch at "); qprintn((uint32_t) &INSTR( rom_addr )); \
    qprint(" (ROM: "); qprintn(rom_addr); qprint(") to "); qprintn((uint32_t)(dest_addr)); qprint("\n"); \
    INSTR( rom_addr ) = THUMB_BLX_INSTR( &INSTR( rom_addr ), (dest_addr) )

static void my_bzero32(void* buf, size_t len)
{
    bzero32(buf, len);
}

static void my_create_init_task(uint32_t a, uint32_t b, uint32_t c)
{
    create_init_task(a, b, c);
}

static int32_t get_immediate_bits(uint32_t instr)
{
    // Given a T2 encoded mov.w instruction, as a 32-bit
    // little-endian read from the instruction address,
    // returns the immediate bits, or -1 for error.

    // Rom uses mov.w, which is encoding T2 from here:
    // https://developer.arm.com/documentation/ddi0406/c/Application-Level-Architecture/Instruction-Details/Alphabetical-list-of-instructions/MOV--immediate-?lang=en
    // (but, for me, the webpage renders badly, you need the PDF to get the real bit pattern)
    //
    // 15 14 13 12 11 10  9  8  7  6  5  4  3  2  1  0|15 14 13 12 11 10  9  8  7  6  5  4  3  2  1  0|
    // ------------------------------------------------------------------------------------------------
    //  1  1  1  1  0| i| 0| 0  0  1  0| S| 1  1  1  1| 0|  imm3  |     Rd    |          imm8         |
    //
    // d = UInt(Rd);  setflags = (S == '1');  (imm32, carry) = ThumbExpandImm_C(i:imm3:imm8, APSR.C);
    // if d IN {13,15} then UNPREDICTABLE;
    //

    // Mangle the instr into Thumb form, 2 16-bit big-endian words.
    // This allows easier comparison with the above encoding docs.
    uint32_t orig_instr = instr;
    instr = (orig_instr & 0xff000000) >> 0x10;
    instr |= (orig_instr & 0x00ff0000) >> 0x10;
    instr |= (orig_instr & 0x0000ff00) << 0x10;
    instr |= (orig_instr & 0x000000ff) << 0x10;

    // Masks derived from the above info
    uint32_t required_on_bits =  0b11110000010011110000000000000000;
    uint32_t required_off_bits = 0b00001011101000001000000000000000;
    if ((instr & required_on_bits) != required_on_bits)
    {
        qprint("Missing required on bits in instr, doesn't look like mov.w\n");
        qprintn(instr & required_on_bits); qprint("\n");
        return -1;
    }
    if ((~instr & required_off_bits) != required_off_bits)
    {
        qprint("Missing required off bits in instr, doesn't look like mov.w\n");
        qprintn(~instr & required_off_bits); qprint("\n");
        return -1;
    }

    uint32_t imm = (instr & (1 << 26)) >> 15;
    imm |= (instr & 0b111000000000000) >> 4;
    imm |= (instr & 0b11111111);

    // we don't handle the weirder immediate encodings
    // (see ThumbExpandImm_C())
    if ((imm & 0b110000000000) == 0)
    {
        qprint("Unhandled encoding! "); qprintn(imm); qprint("\n");
        return -1;
    }

    return imm;
}

static uint32_t encode_mov(uint32_t old_instr, uint32_t val)
{
    // old_instr should be a mov.w instruction in T2 encoding,
    // as a 32-bit little-endian read from the instruction address.
    // 
    // We attempt to modify this instruction to change the constant,
    // preserving the register.
    //
    // Not all values can be encoded.
    //
    // val should be aligned to MOV_ALIGNMENT.  Actual encoding
    // is not this strict but it makes the sums easier.
    //
    // Returns 0 on error.

    int32_t imm = get_immediate_bits(old_instr);
    qprint("Encoding mov.w for value: "); qprintn(val); qprint("\n");
    if (imm == -1)
        return 0;

    if (val % MOV_ALIGNMENT != 0)
        return 0;

    if (MOV_ALIGNMENT != 0x8000)
    {
        qprint("Unexpected MOV_ALIGNMENT.  You're going to have to fix encode_mov logic\n");
        qprintn(MOV_ALIGNMENT); qprint("\n");
        // the following logic may assume 0x8000 alignment, sorry
        return 0;
    }

    if (val > (0xff << 0xf)) // max of aligned-down 8MB
    {
        qprint("Value greater than 8MB, rejecting: "); qprintn(val); qprint("\n");
        return 0;
    }

    // determine how to represent val given constraints on the immediate bits

    // locate end bits
    uint32_t val_check = val;
    uint32_t shift_count_l = 0;
    uint32_t shift_count_r = 0;
    while ((val_check & 0x80000000) != 0x80000000 && shift_count_l < 31)
    {
        val_check = val_check << 1;
        shift_count_l += 1;
    }
    val_check = val;
    while ((val_check & 0x1) != 0x1 && shift_count_r < 31)
    {
        val_check = val_check >> 1;
        shift_count_r += 1;
    }
    qprint("Shift count: "); qprintn(shift_count_l); qprintn(shift_count_r); qprint("\n");
    uint32_t val_width = 32 - (shift_count_l + shift_count_r);
    if (val_width > 8)
    {
        qprint("val width too high, shouldn't happen: \n"); qprintn(val); qprint("\n");
        // I think the alignment and max checks mean this is impossible
        return 0;
    }

    // during decoding an implied leading bit is added, so we must
    // shift our value so our leading bit is high-bit in the byte
    // we get for value.  Later we mask this out.
    uint32_t shift_count = 0;
    while ((val_check & 0x80) != 0x80 && shift_count < 8)
    {
        val_check = val_check << 1;
        shift_count += 1;
    }
    uint32_t imm8 = val_check & 0x7f;

    // determine the amount of ROR needed to turn our byte
    // into the desired value
    uint32_t ror_count = 0;
    while (val_check < val && ror_count < 32)
    {
        val_check = val_check << 1;
        ror_count += 1;
    }
    ror_count = 32 - ror_count;
    qprint("ROR count: "); qprintn(ror_count); qprint("\n");

    // move the 5 ror bits into the right places
    if (ror_count % 1)
        imm8 |= 0x80;
    ror_count = ror_count >> 1;

    uint32_t imm3 = 0;
    imm3 = ror_count & 0b111;
    ror_count = ror_count >> 3;
    // ror_count is now i, a single bit

    // adjust the instruction with the ror bits (i + imm3 + high bit of imm8),
    // and the 7 low bits of imm8.
    //
    // 15 14 13 12 11 10  9  8  7  6  5  4  3  2  1  0|15 14 13 12 11 10  9  8  7  6  5  4  3  2  1  0|
    // ------------------------------------------------------------------------------------------------
    //  1  1  1  1  0| i| 0| 0  0  1  0| S| 1  1  1  1| 0|  imm3  |     Rd    |          imm8         |

    qprint("i, imm3, imm8: "); qprintn(ror_count); qprintn(imm3); qprintn(imm8); qprint("\n");

    qprintn(old_instr); qprint("\n");
    uint32_t instr = old_instr & 0x8f00fbff;// wipe the i bits
    instr |= (imm8 << 16);
    instr |= (imm3 << 28);
    instr |= (ror_count << 10);

    qprintn(instr); qprint("\n");

    return instr;
}

static uint32_t decode_mov(uint32_t instr)
{
    // Only handles mov.w T2 encoding.
    // Returns the constant value used, e.g.
    // mov.w r0, #0x12300 would return 0x12300.
    //
    // Should be passed a 32-bit little-endian read
    // from the instruction address.
    //
    // Does not handle the more exotic immediate encodings.
    //
    // Returns 0 on error.

    int32_t imm = get_immediate_bits(instr);
    if (imm == -1)
        return 0;
    // We have the immediate bits.  Now we must expand them.
    // get_immediate_bits() errors if the encoding is unusual,
    // so we know we have the "else" case in ThumbExpandImm_C().

    // ThumbExpandImm_C()
    // ==================
    // (bits(32), bit) ThumbExpandImm_C(bits(12) imm12, bit carry_in)
    // if imm12<11:10> == ‘00’ then
    //     case imm12<9:8> of
    //         when ‘00’
    //             imm32 = ZeroExtend(imm12<7:0>, 32);
    //         when ‘01’
    //             if imm12<7:0> == ‘00000000’ then UNPREDICTABLE;
    //             imm32 = ‘00000000’ : imm12<7:0> : ‘00000000’ : imm12<7:0>;
    //         when ‘10’
    //             if imm12<7:0> == ‘00000000’ then UNPREDICTABLE;
    //             imm32 = imm12<7:0> : ‘00000000’ : imm12<7:0> : ‘00000000’;
    //         when ‘11’
    //             if imm12<7:0> == ‘00000000’ then UNPREDICTABLE;
    //             imm32 = imm12<7:0> : imm12<7:0> : imm12<7:0> : imm12<7:0>;
    //             carry_out = carry_in;
    // else
    //    unrotated_value = ZeroExtend(‘1’:imm12<6:0>, 32);
    //    (imm32, carry_out) = ROR_C(unrotated_value, UInt(imm12<11:7>));
    // return (imm32, carry_out);

    uint32_t val = (imm & 0b1111111);
    val |= (1 << 7);
    // rotate right
    uint32_t rotate_size = (imm & 0b111110000000) >> 7; // max 31
    uint32_t val_l = (val << (32 - rotate_size));
    uint32_t val_r = val >> rotate_size;
    val = val_l | val_r;

    return val;
}

void
__attribute__((noreturn,noinline,naked))
copy_and_restart( int offset )
{
    zero_bss();

    // Copy the firmware to somewhere safe in memory
    const uint8_t * const firmware_start = (void*) ROMBASEADDR;
    const uint32_t firmware_len = RELOCSIZE;
    uint32_t * const new_image = (void*) RELOCADDR;

    blob_memcpy( new_image, firmware_start, firmware_start + firmware_len );

    /*
     * in cstart() make these changes:
     * calls bzero(), then loads bs_end and calls
     * create_init_task
     */

    // Reserve memory by reducing the user_mem pool and, if necessary for the
    // requested size, moving up the start of sys_objs and sys_mem.
    // ML goes in the gap.  RESTARTSTART defines the start address of the gap,
    // ML_RESERVED_MEM the size.
    uint32_t ml_reserved_mem = ML_RESERVED_MEM;

    // align up to 8, DryOS does this for the various mem regions
    // that we are adjusting.
    if (ml_reserved_mem % 8 != 0)
        ml_reserved_mem += 8 - ml_reserved_mem % 8;

    uint32_t sys_objs_start = *(int *)PTR_SYS_OBJS_START;
    if (RESTARTSTART > sys_objs_start)
    {   // I don't know of a reason to extend user_mem or leave a gap so this
        // is probably a mistake.
        qprint("[BOOT] unexpected RESTARTSTART address > sys_objs_start\n");
        qprint("RESTARTSTART: "); qprintn(RESTARTSTART); qprint("\n");
        qprint("sys_objs_start:"); qprintn(sys_objs_start); qprint("\n");
        goto fail;
    }

    // the RESTARTSTART > sys_objs_start guard means mem to steal from user will be positive
    uint32_t steal_from_user_size = sys_objs_start - RESTARTSTART;
    if (steal_from_user_size > ML_MAX_USER_MEM_STOLEN)
    {
        qprint("[BOOT] RESTARTSTART possibly unsafe, too much stolen from user_mem\n");
        qprint("steal_from_user_size: "); qprintn(steal_from_user_size); qprint("\n");
        goto fail;
    }

    // obtain original sys_mem_start from mov.w
    uint32_t mov_sys_mem_start = *(uint32_t *)(MOV_SYS_MEM_START);
    if (mov_sys_mem_start != 0x103af44f) // mov.w r0, #0x2e8000
    {
        // So far all D6 cams I've looked at have the same value,
        // making this cautious check okay.  May not be universally true.
        qprint("Unexpected asm, bailing: "); qprintn(*(int *)(HIJACK_FIXBR_BZERO32 + 8)); qprint("\n");
        goto fail;
    }
    uint32_t old_sys_mem_start = decode_mov(mov_sys_mem_start);
    qprint("sys_mem_start: "); qprintn(old_sys_mem_start); qprint("\n");
    if (old_sys_mem_start == 0)
        goto fail;

    // work out how far to move sys_objs and sys_mem
    int32_t sys_mem_offset_increase = ml_reserved_mem - steal_from_user_size;
    // align this, to keep sys_mem_start aligned later on
    if (sys_mem_offset_increase % MOV_ALIGNMENT != 0)
        sys_mem_offset_increase += MOV_ALIGNMENT - sys_mem_offset_increase % MOV_ALIGNMENT;

    if (sys_mem_offset_increase < 0)
    {
        qprint("[BOOT] sys_mem_offset_increase was negative, shouldn't happen!\n");
        qprint("sys_mem_offset_increase: "); qprintn(sys_mem_offset_increase); qprint("\n");
        goto fail;
    }
    if (sys_mem_offset_increase > ML_MAX_SYS_MEM_INCREASE)
    {
        qprint("[BOOT] sys_mem_offset_increase possibly unsafe, not tested this high, aborting\n");
        qprint("sys_mem_offset_increase: "); qprintn(sys_mem_offset_increase); qprint("\n");
        goto fail;
    }

    // sys_mem_start wants to be aligned to 0x1000, 4kB increments,
    // this makes encoding mov instruction easier later on.
    //
    // Again, all D6 cams so far seen start aligned enough,
    // adding an aligned value will preserve this.
    uint32_t new_sys_mem_start = old_sys_mem_start + sys_mem_offset_increase;
    if (new_sys_mem_start % MOV_ALIGNMENT != 0)
    {
        qprint("[BOOT] sys_mem_start wasn't aligned, bailing\n");
        qprint("new_sys_mem_start: "); qprintn(new_sys_mem_start); qprint("\n");
    }

    qprint("[BOOT] reserving memory: "); qprintn(ml_reserved_mem); qprint("\n");
    qprint("before: user_mem_size = "); qprintn(INSTR(PTR_USER_MEM_SIZE)); qprint("\n");
    // shrink user_mem
    INSTR(PTR_USER_MEM_SIZE) -= steal_from_user_size;
    qprint(" after: user_mem_size = "); qprintn(INSTR(PTR_USER_MEM_SIZE)); qprint("\n");

    // Move sys_objs and sys_mem later in ram.
    //
    // On D78, this is easier as the relevant constants are stored in mem.
    //
    // On D6, some constants are encoded directly in instructions, so we must patch.
    // The mov.w we're using to patch only allows 8 significant bits in the address.
    //
    // We expect the setup movs to be directly after HIJACK_FIXBR_BZERO32 address,
    // like this:
    //
    // 01 f3 0c e8     blx        bzero_32     <--- this is HIJACK_FIXBR_BZERO32 address
    // 4f f4 64 21     mov.w      r1,#0xe4000  <--- sys_mem_len (don't care, we don't change it)
    // 4f f4 3a 10     mov.w      r0,#0x2e8000 <--- sys_mem_start and sys_objs_end
    // 00 22           movs       r2,#0x0
    // cd e9 01 01     strd       r0,r1,[sp,#0x4]
    //
    // Bad Things will likely occur if this is done incorrectly, so we check
    // mem is as expected before proceeding.
    if (*(uint32_t *)(HIJACK_FIXBR_BZERO32 + 4) != 0x2164f44f) // mov.w r1, #0xe4000
    {
        qprint("Unexpected asm, bailing: "); qprintn(*(int *)(HIJACK_FIXBR_BZERO32 + 4)); qprint("\n");
        goto fail;
    }
    if (MOV_SYS_MEM_START != HIJACK_FIXBR_BZERO32 + 8)
    {   // We expect MOV_SYS_MEM_START to be a fixed distance from blx bzero_32,
        // hitting this condition suggests this changed in some future rom...
        // That's fine, but you'll have to check / modify code in this file;
        // this error is there to remind you.
        qprint("Unexpected MOV_SYS_MEM_START offset\n");
        goto fail;
    }
    if (*(uint32_t *)(HIJACK_FIXBR_BZERO32 + 0xc) != 0xe9cd2200)
    {
        qprint("Unexpected asm, bailing: "); qprintn(*(int *)(HIJACK_FIXBR_BZERO32 + 0xc)); qprint("\n");
        goto fail;
    }

    INSTR(PTR_SYS_OBJS_START) += sys_mem_offset_increase;
    uint32_t mov_instr = encode_mov(mov_sys_mem_start, new_sys_mem_start);
    decode_mov(mov_instr); // SJE just a test, remove line
    qprintn(mov_instr); qprint("\n");
    if (mov_instr == 0)
        goto fail;
    INSTR(MOV_SYS_MEM_START) = mov_instr;
//    INSTR(HIJACK_FIXBR_BZERO32 + 8) = 0x105af44f; // SJE FIXME this should be computed from sys_mem_offset_increase.
//                                                  // Currently this is hard-coded as +0x80000 over 0x2e8000
    // see http://shell-storm.org/online/Online-Assembler-and-Disassembler/?inst=mov.w++++++r0%2C%230x358000%0D%0A&arch=arm-t&as_format=inline#assembly

    // Fix the calls to bzero32() and create_init_task()
    FIXUP_BRANCH( HIJACK_FIXBR_BZERO32, my_bzero32 );
    FIXUP_BRANCH( HIJACK_FIXBR_CREATE_ITASK, my_create_init_task );

    // Set our init task to run instead of the firmware one
    qprint("[BOOT] changing init_task from "); qprintn(INSTR( HIJACK_INSTR_MY_ITASK ));
    qprint("to "); qprintn((uint32_t) my_init_task); qprint("\n");
    INSTR( HIJACK_INSTR_MY_ITASK ) = (uint32_t) my_init_task;
    
    // Make sure that our self-modifying code clears the cache
    sync_caches();

    // We enter after the signature, avoiding the
    // relocation jump that is at the head of the data
    // this is Thumb code
    thunk __attribute__((long_call)) reloc_entry = (thunk)( RELOCADDR + 0xC + 1 );
    reloc_entry();

    // Unreachable
fail:
    while(1)
        ;
}
