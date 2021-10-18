/**
 * Camera internals for 200D 1.0.0
 */

/** This camera has a DIGIC VII chip */
#define CONFIG_DIGIC_VII

/** Digic 7 does not have bitmap font in ROM, try to load it from card **/
#define CONFIG_NO_BFNT

/* has LV */
#define CONFIG_LIVEVIEW

/* enable state objects hooks */
#define CONFIG_STATE_OBJECT_HOOKS
