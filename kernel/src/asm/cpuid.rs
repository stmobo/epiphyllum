fn cpuid(in_eax: u32) -> (u32, u32, u32, u32) {
    let eax: u32;
    let ebx: u32;
    let ecx: u32;
    let edx: u32;

    unsafe {
        asm!("cpuid" : "={eax}"(eax), "={ebx}"(ebx), "={ecx}"(ecx), "={edx}"(edx) : "0"(in_eax) :: "volatile");
    }

    (eax, ebx, ecx, edx)
}

#[derive(Debug, Clone)]
pub struct BasicProcessorInfo {
    eax: u32,
    ebx: u32,
    ecx: u32,
    edx: u32,
}

impl BasicProcessorInfo {
    pub fn new() -> BasicProcessorInfo {
        let (eax, ebx, ecx, edx) = cpuid(1);
        BasicProcessorInfo { eax, ebx, ecx, edx }
    }

    pub fn stepping(&self) -> u8 {
        (self.eax & 0x0F) as u8
    }

    pub fn model(&self) -> u8 {
        let family_id = (self.eax >> 8) & 0x0F;
        if family_id == 6 || family_id == 15 {
            let ext_model = (self.eax >> 12) & 0xF0;
            (ext_model | ((self.eax >> 4) & 0x0F)) as u8
        } else {
            ((self.eax >> 4) & 0x0F) as u8
        }
    }

    pub fn family_id(&self) -> u16 {
        let f1 = (self.eax >> 8) & 0x0F;
        if f1 == 15 {
            (((self.eax >> 20) & 0xFF) + 15) as u16
        } else {
            f1 as u16
        }
    }

    pub fn lapic_id(&self) -> u8 {
        ((self.ebx >> 24) & 0xFF) as u8
    }

    pub fn check_feature(&self, feature: FeatureFlags) -> bool {
        let feature_bit = feature as u32;
        if feature_bit < 32 {
            return (self.edx & (1 << feature_bit)) != 0;
        } else if feature_bit < 64 {
            return (self.ecx & (1 << (feature_bit - 32))) != 0;
        }

        false
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
#[repr(u32)]
#[allow(non_camel_case_types)]
pub enum FeatureFlags {
    /* EDX feature flags: */
    FPU = 0,     /* on-chip x87 FPU */
    VME = 1,     /* virtual 8086 extensions */
    DE = 2,      /* Debug extensions */
    PSE = 3,     /* Page size extension */
    TSC = 4,     /* Time stamp counter */
    MSR = 5,     /* Model-specific registers */
    PAE = 6,     /* Physical address extension */
    MCE = 7,     /* Machine check architecture */
    CX8 = 8,     /* CMPXCHG8 instruction */
    APIC = 9,    /* Onboard APIC */
    SEP = 11,    /* SYSENTER / SYSEXIT instructions */
    MTRR = 12,   /* Memory Type-Range Registers */
    PGE = 13,    /* Page Global Enable bit */
    MCA = 14,    /* Machine Check Architecture */
    CMOV = 15,   /* Conditional MOV */
    PAT = 16,    /* Page Attribute Table */
    PSE_36 = 17, /* 36-bit page size extensions*/
    PSN = 18,    /* Processor serial number */
    CLFSH = 19,  /* CLFLUSH */
    DS = 21,     /* Debug store */
    ACPI = 22,   /* ACPI thermal control MSRs */
    MMX = 23,    /* MMX instructions */
    FXSR = 24,   /* FXSAVE / FXRESTOR */
    SSE = 25,    /* SSE instructions */
    SSE2 = 26,   /* SSE2 instructions */
    SS = 27,     /* Self-snoop for CPU cache */
    HTT = 28,    /* Hyperthreading */
    TM = 29,     /* Automatic thermal monitoring */
    IA64 = 30,   /* IA64 emulation flag */
    PBE = 31,    /* Pending Break Enable wakeup capability */

    /* ECX feature flags */
    SSE3 = 32,         /* SSE3 instructions */
    PCLMULQDQ = 33,    /* PCLMULQDQ instructions */
    DTES64 = 34,       /* 64-bit Debug Store */
    MONITOR = 35,      /* MONITOR and MWAIT instructions */
    DS_CPL = 36,       /* CPL-qualified Debug Store */
    VMX = 37,          /* Virtual Machine Extensions */
    SMX = 38,          /* Safer Mode Extensions */
    EST = 39,          /* Enhanced SpeedStep */
    TM2 = 40,          /* Thermal Monitor 2 */
    SSSE3 = 41,        /* Supplemental SSE3 instructions */
    CNXT_ID = 42,      /* L1 Context ID */
    SDBG = 43,         /* Silicon Debug Interface */
    FMA = 44,          /* Fused Multiply-Add */
    CX16 = 45,         /* CMPXCHG16B instruction */
    XTPR = 46,         /* Task priority message disable */
    PDCM = 47,         /* Performance monitoring and debugging capabilities */
    PCID = 49,         /* Process Context IDs */
    DCA = 50,          /* DMA Direct Cache Access */
    SSE4_1 = 51,       /* SSE 4.1 instructions */
    SSE4_2 = 52,       /* SSE 4.2 instructions */
    X2_APIC = 53,      /* x2APIC */
    MOVBE = 54,        /* MOVBE instruction */
    POPCNT = 55,       /* POPCNT instruction */
    TSC_DEADLINE = 56, /* APIC TSC Deadline capability */
    AES = 57,          /* AES instructions */
    XSAVE = 58,        /* XSAVE etc. instructions */
    OS_XSAVE = 59,     /* XSAVE enabled by OS */
    AVX = 60,          /* AVX instructions */
    F16C = 61,         /* Half-precision floating point */
    RDRND = 62,        /* on-chip RNG */
    HYPERVISOR = 63,   /* Hypervisor present */
}
