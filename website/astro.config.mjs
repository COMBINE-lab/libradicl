// @ts-check
import { defineConfig } from 'astro/config';
import starlight from '@astrojs/starlight';
import remarkGfm from 'remark-gfm';

// GitHub Pages: site + base. The repo deploys to
// https://combine-lab.github.io/libradicl/.
export default defineConfig({
  site: 'https://combine-lab.github.io',
  base: '/libradicl',
  // GitHub-Flavored Markdown (tables, strikethrough, autolinks) is applied to
  // `.md` by default but NOT to `.mdx`; add remark-gfm explicitly so the many
  // tables in the `.mdx` pages render.
  markdown: {
    remarkPlugins: [remarkGfm],
  },
  integrations: [
    starlight({
      title: 'RAD format',
      description:
        'The Reduced Alignment Data (RAD) format — a compact, self-describing binary format for mapped sequencing reads, produced by piscem and salmon and consumed by alevin-fry.',
      social: [
        {
          icon: 'github',
          label: 'GitHub',
          href: 'https://github.com/COMBINE-lab/libradicl',
        },
      ],
      editLink: {
        baseUrl: 'https://github.com/COMBINE-lab/libradicl/edit/develop/website/',
      },
      sidebar: [
        {
          label: 'Introduction',
          items: [
            { label: 'What is RAD?', slug: 'introduction/what-is-rad' },
            { label: 'Motivation & design', slug: 'introduction/design' },
          ],
        },
        {
          label: 'The format',
          items: [
            { label: 'File structure', slug: 'format/overview' },
            { label: 'Prelude & header', slug: 'format/prelude-and-header' },
            { label: 'Type system', slug: 'format/type-system' },
            { label: 'Tag sections', slug: 'format/tags' },
            { label: 'Chunks & records', slug: 'format/chunks-and-records' },
          ],
        },
        {
          label: 'Versioning & roles',
          items: [
            { label: 'Spec versioning', slug: 'versioning/spec-versioning' },
            { label: 'Tag roles', slug: 'versioning/tag-roles' },
          ],
        },
      ],
    }),
  ],
});
