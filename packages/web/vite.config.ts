import { defineConfig } from 'vite';
import react from '@vitejs/plugin-react';

// `base` must match the GitHub Pages path: https://<user>.github.io/<repo>/
// Set DYP_BASE in CI from the repository name.
export default defineConfig({
  plugins: [react()],
  base: process.env.DYP_BASE ?? '/',
  build: { outDir: 'dist', emptyOutDir: true },
});
