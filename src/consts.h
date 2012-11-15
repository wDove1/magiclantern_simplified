
/* will get undefined if camera model is known */
#define CONFIG_ERROR

#ifdef CONFIG_550D
#include "../platform/550D.109/consts.h"
#undef CONFIG_ERROR
#endif

#ifdef CONFIG_60D
#include "../platform/60D.111/consts.h"
#undef CONFIG_ERROR
#endif

#ifdef CONFIG_600D
#include "../platform/600D.102/consts.h"
#undef CONFIG_ERROR
#endif

#ifdef CONFIG_50D
#include "../platform/50D.109/consts.h"
#undef CONFIG_ERROR
#endif

#ifdef CONFIG_500D
#include "../platform/500D.111/consts.h"
#undef CONFIG_ERROR
#endif

#ifdef CONFIG_1100D
#include "../platform/1100D.105/consts.h"
#undef CONFIG_ERROR
#endif

#ifdef CONFIG_5D2
#include "../platform/5D2.212/consts.h"
#undef CONFIG_ERROR
#endif

#ifdef CONFIG_5D3
#include "../platform/5D3.113/consts.h"
#undef CONFIG_ERROR
#endif

#ifdef CONFIG_5DC
#include "../platform/5DC.111/consts.h"
#undef CONFIG_ERROR
#endif

#ifdef CONFIG_7D_MASTER
#include "../platform/7D_MASTER.203/consts.h"
#undef CONFIG_ERROR
#endif

#ifdef CONFIG_7D
#include "../platform/7D.203/consts.h"
#undef CONFIG_ERROR
#endif

#ifdef CONFIG_40D
#include "../platform/40D.111/consts.h"
#undef CONFIG_ERROR
#endif

#ifdef CONFIG_EOSM
#include "../platform/EOSM.100/consts.h"
#undef CONFIG_ERROR
#endif

#ifdef CONFIG_ERROR
#error This file does not contain this camera model. Please add it.
#endif