/** \file
 * Startup code for DIGIC 6
 */

#include "dryos.h"
#include "boot.h"

/** These are called when new tasks are created */
static int my_init_task(int a, int b, int c, int d);

/** This just goes into the bss */
#define RELOCSIZE 0x3D100  // look in HIJACK macros for the highest address, and subtract ROMBASEADDR; 0x50000 was too much for 750D

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
    ml_reserved_mem = ML_RESERVED_MEM;

    // align up to 8, DryOS does this for the various mem regions
    // that we are adjusting.
    if (ml_reserved_mem % 8 != 0)
        ml_reserved_mem += 8 - ml_reserved_mem % 8;

    uint32_t sys_objs_start = *(int *)PTR_SYS_OBJS_START;
    if (RESTARTSTART > sys_objs_start)
    {   // I don't know of a reason to extend user_mem or leave a gap so this
        // is probably a mistake.
        qprint("[BOOT] unexpected RESTARTSTART address > sys_objs_start\n");
        qprintn(RESTARTSTART);
        qprintn(sys_objs_start);
        goto fail;
    }

    // the RESTARTSTART > sys_objs_start guard means mem to steal from user will be positive
    uint32_t steal_from_user_size = sys_objs_start - RESTARTSTART;
    if (steal_from_user_size > ML_MAX_USER_MEM_STOLEN)
    {
        qprint("[BOOT] RESTARTSTART possibly unsafe, too much stolen from user_mem\n");
        qprintn(steal_from_user_size);
        goto fail;
    }

    int32_t sys_mem_offset_increase = ml_reserved_mem - steal_from_user_size;
    if (sys_mem_offset_increase < 0)
    {
        qprint("[BOOT] sys_mem_offset_increase was negative, shouldn't happen!\n");
        goto fail;
    }
    if (sys_mem_offset_increase > ML_MAX_SYS_MEM_INCREASE)
    {
        qprint("[BOOT] sys_mem_offset_increase possibly unsafe, not tested this high, aborting\n");
        qprintn(sys_mem_offset_increase);
        goto fail;
    }

    qprint("[BOOT] reserving memory: "); qprintn(ml_reserved_mem); qprint("\n");
    qprint("before: user_mem_size = "); qprintn(INSTR(PTR_USER_MEM_SIZE)); qprint("\n");

    // shrink user_mem
    INSTR(PTR_USER_MEM_SIZE) -= steal_from_user_size;
    qprint(" after: user_mem_size = "); qprintn(INSTR(PTR_USER_MEM_SIZE)); qprint("\n");

    // Move sys_objs and sys_mem later in ram.
    // On D78, this is easier as the relevant constants are stored in mem.
    // On D6, some are encoded directly in instructions, so we must patch.
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
    if (*(int *)(HIJACK_FIXBR_BZERO32 + 4) != 0x2164f44f)
        goto fail;
    if (*(int *)(HIJACK_FIXBR_BZERO32 + 8) != 0x103af44f)
        goto fail;
    if (*(int *)(HIJACK_FIXBR_BZERO32 + 0xc) != 0xe9cd2200)
        goto fail;

    INSTR(PTR_SYS_OBJS_START) += sys_mem_offset_increase;
    INSTR(HIJACK_FIXBR_BZERO32 + 8) = 0x105af44f; // SJE FIXME this should be computed from sys_mem_offset_increase.
                                                  // Currently this is hard-coded as +0x80000 over 0x2e8000
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
