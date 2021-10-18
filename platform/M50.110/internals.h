/**
 * Camera internals for EOS M50 1.1.0
 */

/** This camera has a DIGIC VIII chip */
#define CONFIG_DIGIC_VIII

/** Digic 8 does not have bitmap font in ROM, try to load it from card **/
#define CONFIG_NO_BFNT

/** disable SRM for now
 * in current state SRM_AllocateMemoryResourceFor1stJob makes camera crash
 * even if just one buffer is requrested.
 */
#define CONFIG_MEMORY_SRM_NOT_WORKING

/* has LV */
#define CONFIG_LIVEVIEW

/* enable state objects hooks */
#define CONFIG_STATE_OBJECT_HOOKS
