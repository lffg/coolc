pub trait Env {
    const ENTRY_POINT: &str;

    const GLOBAL_PROLOGUE: &str;

    const SECTION_TEXT: &str;
    const SECTION_READ_ONLY_DATA: &str;
    const SECTION_READ_ONLY_RELOCATABLE_DATA: &str;
}

impl Env for Darwin {
    const ENTRY_POINT: &str = "_main";

    const GLOBAL_PROLOGUE: &str = ".intel_syntax noprefix\n\n";

    const SECTION_TEXT: &str = "__TEXT,__text,regular,pure_instructions";
    const SECTION_READ_ONLY_DATA: &str = "__TEXT,__const";
    const SECTION_READ_ONLY_RELOCATABLE_DATA: &str = "__DATA,__const";
}

impl Env for Linux {
    const ENTRY_POINT: &str = "main";

    const GLOBAL_PROLOGUE: &str = concat!(
        ".intel_syntax noprefix\n",
        ".section .note.GNU-stack,\"\",@progbits\n\n",
    );

    const SECTION_TEXT: &str = ".text";
    const SECTION_READ_ONLY_DATA: &str = ".rodata";
    const SECTION_READ_ONLY_RELOCATABLE_DATA: &str = ".data.rel.ro";
}

pub struct Darwin;

pub struct Linux;
