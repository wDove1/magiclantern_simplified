/** \file
 * Entry points into the firmware image.
 *
 * These are the functions that we can call from our tasks
 * in the Canon 1.0.5 firmware for the EOS 6D Mark II.
 *
 */
/*
 * Copyright (C) 2021 Magic Lantern Team
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the
 * Free Software Foundation, Inc.,
 * 51 Franklin Street, Fifth Floor,
 * Boston, MA  02110-1301, USA.
 */

#include <stub.h>

/** Startup **/
NSTUB( ROMBASEADDR, firmware_entry )
THUMB_FN(0xe00400fd,  cstart)                 /* calls bzero32 and create_init_task(..., init_task, ...) */
THUMB_FN(0xdf00d299,  bzero32)                /* zeros out a data structure */
THUMB_FN(0xdf006515,  create_init_task)       /* low-level DryOS initialization */
THUMB_FN(0xe0040225,  init_task)              /* USER_MEM size checking, dmSetup, termDriverInit, stdlibSetup etc */
THUMB_FN(0xe06b0368,  dcache_clean)           /* loop with MCR p15 c7,c10,1; DSB */
THUMB_FN(0xe06b043c,  icache_invalidate)      /* loop with MCR p15 c7,c5,1; c7,c1,6; c7,c1,0; ISB */

/** Tasks **/
THUMB_FN(0xdf008ce7,  task_create)            /* used to start TaskMain, GuiMainTask etc */
THUMB_FN(0xdf008f0b,  task_create_ex)         /* as task_create, but allows selecting CPU for task*/
THUMB_FN(0xdf00880f,  msleep)                 /* argument is always multiple of 10 */
DATA_PTR(    0x1028,  current_task)           /* from task_create; pointer to the current task structure */
DATA_PTR(    0x1010,  current_interrupt)      /* from interrupt handler (VBAR + 0x18); where the interrupt ID is stored */

/** Dumper **/
THUMB_FN(0xe008099e,  dump_file)              /* tries to save a file to either "A:/%s" or "B:/%s"; calls FIO_RemoveFile/CreateFile/WriteFile/CloseFile/Flush */

/** Memory info **/
THUMB_FN(0xe02898d8,  malloc_info)            /* Malloc Information */
THUMB_FN(0xe0289970,  sysmem_info)            /* System Memory Information */
THUMB_FN(0xe0202728,  memmap_info)            /* Exception vector, DRYOS system memory etc */
THUMB_FN(0xe0175b46,  smemShowFix)            /* Common Lower, Common Upper etc */

/** Memory allocation **/
THUMB_FN(0xdf007b58, _AllocateMemory)
THUMB_FN(0xdf007d10, _FreeMemory)
THUMB_FN(0xdf0079e2,  GetMemoryInformation)   /* called from AllocateMemory */
THUMB_FN(0xdf007946,  GetSizeOfMaxRegion)
THUMB_FN(0xdf00ac54, _alloc_dma_memory)
THUMB_FN(0xdf00ac80, _free_dma_memory)
THUMB_FN(0xe070a8ea,  malloc)
THUMB_FN(0xe070a922,  free)

/** Debug messages **/
THUMB_FN(0xdf006e6c,  DryosDebugMsg)          /* lots of debug messages; format string is third argument */

/** DMA **/
THUMB_FN(0xe01e565a,  dma_memcpy)

/** Eventprocs (call by name) **/
THUMB_FN(0xe04e7356,  call)                   /* many functions called by name (lv_start, lv_stop etc) */

/** File I/O **/
THUMB_FN(0xe04e59b4, _FIO_OpenFile)
THUMB_FN(0xe04e5a1e, _FIO_CreateFile)
THUMB_FN(0xe04e5ad8, _FIO_ReadFile)
THUMB_FN(0xe04e5b7e, _FIO_WriteFile)
THUMB_FN(0xe04e70fc,  FIO_SeekSkipFile)
THUMB_FN(0xe04e5bf0,  FIO_CloseFile)
THUMB_FN(0xe04e6518, _FIO_CreateDirectory)
//THUMB_FN(0x,  FIO_FindFirst)
THUMB_FN(0xe04e6942, _FIO_FindFirstEx)
THUMB_FN(0xe04e69da,  FIO_FindNextEx)
THUMB_FN(0xe04e6922,  FIO_FindClose)
THUMB_FN(0xe04e5d0e, _FIO_GetFileSize)
THUMB_FN(0xe04e5a8c, _FIO_RemoveFile)
THUMB_FN(0xe04e6392, _FIO_RenameFile)
THUMB_FN(0xe04e663c,  FIO_Flush)               // to be called after FIO_CloseFile?


////////////////////////////////
// filled these in as I went along, be sure to check for duplicates above,
// I might copy-paste badly into there, these ones should be preferred:
THUMB_FN(0xe06171f0,  debug_assert) // DRYOS_ASSERT_HANDLER related
