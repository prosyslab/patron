int main(int argc, char* argv[]) {
    char * filename = input();
    int *flowfp = fopen(filename, "rb");

    unsigned int hdr, width, height;

    fread(&hdr, sizeof(hdr), 1, flowfp);
	fread(&width, sizeof(width), 1, flowfp);
	fread(&height, sizeof(height), 1, flowfp); 

    void* flow = malloc(width * height); // IO snk

    return 0;
}
